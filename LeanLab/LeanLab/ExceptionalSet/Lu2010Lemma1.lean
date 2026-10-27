/-
P0095 W. C. Lu 2010, Lemma 1, p. 2361 and its proof p. 2362. Unit U-6843, CLOUD MANUAL-M1,
2026-10-21, track T1.

Lemma 1 says D(k) = D̃(k) + O(N^{1-0.0001}) for |k - N| ≤ d N^-0.00011. Its proof has two
steps: orthogonality turns D̃(k) into the t-integral
  `Dt N k = ∫_a^b Σ_{td < n ≤ td+d, N-td-d < m ≤ N-td, n+m=k} Λ(n) Λ(m) dt`,
and then "= Σ_{ad+d<n≤bd} Λ(n)Λ(k-n) + O(N^{1-0.0001})". This file PROVES the second step,
with the error the printed argument gives:
  |Dt N k - D(k)| ≤ (|N-k|/d)(k+1) log²k + (2d+2) log²k ≤ 7 N^0.9999 log²(2N),
and so |Dt N k - D(k)| ≤ N^0.99995 for every large N on the window.

QUESTION Q-6843a, recorded only: the paper states O(N^{1-0.0001}) with absolute O-constants,
p. 2361 "the O-s always are absolute". The two edge ranges ad < n ≤ ad+d and bd < n < bd+d
carry partial t-weight and hold about 2d terms Λ(n)Λ(k-n); bounding them needs either the
trivial log²N, as here, or an upper sieve, which still leaves a factor 𝔖(k), unbounded in k.
The printed one-line proof does not give the absolute O(N^0.9999); every later use only needs
N^{1-0.0001+ε}, so the Theorem is unaffected.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach itself is OPEN.
-/
import Mathlib
import LeanLab.ExceptionalSet.Lu2010Assembly

namespace LeanLab.ExceptionalSet.Lu2010Lemma1
open Real Filter Topology Finset ArithmeticFunction MeasureTheory
  LeanLab.ExceptionalSet LeanLab.ExceptionalSet.Lu2010Assembly

/-- The set of `t` with `td < n ≤ td + d` and `N - td - d < k - n ≤ N - td`, the summation
condition of the integrand in the proof of Lemma 1, with `m = k - n`. -/
def tset (N k n : ℕ) : Set ℝ :=
  {t | t * dd N < n ∧ (n : ℝ) ≤ t * dd N + dd N ∧
    (N : ℝ) - t * dd N - dd N < (k : ℝ) - n ∧ (k : ℝ) - n ≤ N - t * dd N}

/-- The proof of Lemma 1, first line after orthogonality:
`∫_a^b Σ_{n+m=k, td<n≤td+d, N-td-d<m≤N-td} Λ(n)Λ(m) dt`. -/
noncomputable def Dt (N k : ℕ) : ℝ :=
  ∫ t in Set.Icc (aa N) (bb N),
    ∑ n ∈ range (k + 1), (tset N k n).indicator (fun _ => Λ n * Λ (k - n)) t

theorem dd_pos {N : ℕ} (hN : 0 < N) : 0 < dd N := rpow_pos_of_pos (by exact_mod_cast hN) _

theorem tset_eq {N k n : ℕ} (hN : 0 < N) :
    tset N k n = Set.Ico (n / dd N - 1) (n / dd N) ∩
      Set.Ioc (((N : ℝ) - k + n) / dd N - 1) (((N : ℝ) - k + n) / dd N) := by
  have hd := dd_pos hN
  ext t
  simp only [tset, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ico, Set.mem_Ioc]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [sub_le_iff_le_add, div_le_iff₀ hd]; linarith
    · rw [lt_div_iff₀ hd]; linarith
    · rw [sub_lt_iff_lt_add, div_lt_iff₀ hd]; linarith
    · rw [le_div_iff₀ hd]; linarith
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    rw [sub_le_iff_le_add, div_le_iff₀ hd] at h1
    rw [lt_div_iff₀ hd] at h2
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hd] at h3
    rw [le_div_iff₀ hd] at h4
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem tset_measurable {N k n : ℕ} (hN : 0 < N) : MeasurableSet (tset N k n) := by
  rw [tset_eq hN]; exact measurableSet_Ico.inter measurableSet_Ioc

/-- The `t`-weight of the term `n`. -/
noncomputable def w (N k n : ℕ) : ℝ := (volume (tset N k n ∩ Set.Icc (aa N) (bb N))).toReal

/-- Tonelli for a finite sum: `Dt = Σ_n Λ(n)Λ(k-n) w(n)`. -/
theorem Dt_eq {N : ℕ} (hN : 0 < N) (k : ℕ) :
    Dt N k = ∑ n ∈ range (k + 1), Λ n * Λ (k - n) * w N k n := by
  unfold Dt
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n _
    rw [setIntegral_indicator (tset_measurable hN), setIntegral_const, smul_eq_mul, mul_comm,
      Set.inter_comm]
    rfl
  · intro n _
    exact (integrableOn_const (by simp [Real.volume_Icc])).indicator (tset_measurable hN)

theorem w_nonneg (N k n : ℕ) : 0 ≤ w N k n := ENNReal.toReal_nonneg

theorem w_le_one {N : ℕ} (hN : 0 < N) (k n : ℕ) : w N k n ≤ 1 := by
  unfold w
  have h : volume (tset N k n ∩ Set.Icc (aa N) (bb N)) ≤ volume (Set.Ico ((n : ℝ) / dd N - 1) (n / dd N)) := by
    apply measure_mono
    rw [tset_eq hN]
    exact Set.inter_subset_left.trans Set.inter_subset_left
  rw [Real.volume_Ico] at h
  have : ((n : ℝ) / dd N - (n / dd N - 1)) = 1 := by ring
  rw [this, ENNReal.ofReal_one] at h
  have := ENNReal.toReal_mono ENNReal.one_ne_top h
  simpa using this

/-- The weight is zero unless `a < n/d < b + 1`. -/
theorem w_eq_zero {N : ℕ} (hN : 0 < N) (k n : ℕ)
    (h : (n : ℝ) / dd N ≤ aa N ∨ bb N + 1 ≤ (n : ℝ) / dd N) : w N k n = 0 := by
  unfold w
  have hsub : tset N k n ∩ Set.Icc (aa N) (bb N) ⊆ {bb N} := by
    intro t ht
    rw [tset_eq hN] at ht
    obtain ⟨⟨⟨h1, h2⟩, _⟩, h3, h4⟩ := ht
    rcases h with h | h
    · exact absurd (lt_of_lt_of_le h2 h) (not_lt.mpr h3)
    · simp only [Set.mem_singleton_iff]; linarith
  have : volume (tset N k n ∩ Set.Icc (aa N) (bb N)) = 0 :=
    measure_mono_null hsub (Real.volume_singleton)
  rw [this]; rfl

/-- Inside `D`'s range, `a + 1 < n/d ≤ b`, the weight is at least `1 - |N-k|/d`. -/
theorem w_ge {N : ℕ} (hN : 0 < N) (k n : ℕ) (h1 : aa N + 1 ≤ (n : ℝ) / dd N)
    (h2 : (n : ℝ) / dd N ≤ bb N) : 1 - |(N : ℝ) - k| / dd N ≤ w N k n := by
  have hd := dd_pos hN
  set u := (n : ℝ) / dd N
  set s := ((N : ℝ) - k + n) / dd N
  have hus : |(N : ℝ) - k| / dd N = |s - u| := by
    have : s - u = ((N : ℝ) - k) / dd N := by simp only [s, u]; field_simp; ring
    rw [this, abs_div, abs_of_pos hd]
  have hsub : Set.Ioo (max (u - 1) (s - 1)) (min u s) ⊆ tset N k n ∩ Set.Icc (aa N) (bb N) := by
    intro t ht
    simp only [Set.mem_Ioo, max_lt_iff, lt_min_iff] at ht
    obtain ⟨⟨ha, hb⟩, hc, he⟩ := ht
    rw [tset_eq hN]
    refine ⟨⟨⟨ha.le, hc⟩, hb, he.le⟩, ?_, ?_⟩ <;> simp only [u] at * <;> linarith
  have hfin : volume (tset N k n ∩ Set.Icc (aa N) (bb N)) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Icc])
      (measure_mono Set.inter_subset_right)
  have hm := ENNReal.toReal_mono hfin (measure_mono hsub)
  rw [Real.volume_Ioo, ENNReal.toReal_ofReal'] at hm
  have hmm : min u s - max (u - 1) (s - 1) = 1 - |s - u| := by
    rcases le_total u s with h | h
    · rw [min_eq_left h, max_eq_right (by linarith), abs_of_nonneg (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith), abs_of_nonpos (by linarith)]; ring
  rw [hmm] at hm
  unfold w
  rw [hus]
  exact (le_max_left _ _).trans hm

/-- `Λ(n) Λ(k-n) ≤ log² k`. -/
theorem term_le (k n : ℕ) : Λ n * Λ (k - n) ≤ Real.log k ^ 2 := by
  have hL : ∀ m, m ≤ k → Λ m ≤ Real.log k := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simp; exact Real.log_natCast_nonneg k
    · exact vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hm))
  rcases le_or_gt n k with h | h
  · have h1 := hL n h
    have h2 := hL (k - n) (Nat.sub_le k n)
    have := mul_le_mul h1 h2 vonMangoldt_nonneg (Real.log_natCast_nonneg k)
    nlinarith
  · have : k - n = 0 := by omega
    rw [this]; simp; positivity

/-- The naturals in `(x, x + d]` number at most `d + 1`. -/
theorem card_Ioc_floor_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ((Ioc ⌊x⌋₊ ⌊y⌋₊).card : ℝ) ≤ y - x + 1 := by
  rw [Nat.card_Ioc]
  have hfl : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hxy
  rw [Nat.cast_sub hfl]
  have h1 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (hx.trans hxy)
  have h2 := Nat.lt_floor_add_one x
  linarith

/-- **Lemma 1, second step, PROVED**: on the window,
`|Dt - D| ≤ (|N-k|/d)(k+1) log²k + (2d+2) log²k`. -/
theorem lemma1_step (N k : ℕ) (hN : 0 < N) :
    |Dt N k - DLu N k| ≤
      |(N : ℝ) - k| / dd N * ((k + 1) * Real.log k ^ 2) + (2 * dd N + 2) * Real.log k ^ 2 := by
  classical
  have hd := dd_pos hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have ha0 : 0 ≤ aa N := by unfold aa; positivity
  have hba : (bb N - aa N) * dd N = N / 3 := bad_mul N hN
  have hab : aa N ≤ bb N := by
    have : 0 ≤ bb N - aa N := by
      by_contra hc; push Not at hc
      have : (bb N - aa N) * dd N < 0 := mul_neg_of_neg_of_pos hc hd
      linarith
    linarith
  have hb0 : 0 ≤ bb N := ha0.trans hab
  set A := ⌊aa N * dd N + dd N⌋₊
  set B := ⌊bb N * dd N⌋₊
  set f : ℕ → ℝ := fun n => Λ n * Λ (k - n) with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg
  have hfk : ∀ n, k < n → f n = 0 := by
    intro n hn; simp only [hf]; rw [show k - n = 0 by omega]; simp
  -- D as a sum over range (k+1)
  have hD : DLu N k = ∑ n ∈ range (k + 1), (if n ∈ Ioc A B then f n else 0) := by
    unfold DLu
    rw [Finset.sum_ite_mem]
    rw [← Finset.sum_filter_of_ne (p := fun n => n ≤ k) (s := Ioc A B)]
    · apply Finset.sum_congr
      · ext n; simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_range, Nat.lt_succ_iff]; tauto
      · intro n _; rfl
    · intro n _ hne
      by_contra hlt; push Not at hlt
      exact hne (hfk n hlt)
  -- the edge set
  set E := (range (k + 1)).filter
    (fun n : ℕ => aa N < (n : ℝ) / dd N ∧ (n : ℝ) / dd N < bb N + 1 ∧ n ∉ Ioc A B) with hE
  have hmemD : ∀ n : ℕ, n ∈ Ioc A B ↔ aa N + 1 < (n : ℝ) / dd N ∧ (n : ℝ) / dd N ≤ bb N := by
    intro n
    simp only [Finset.mem_Ioc, A, B]
    rw [Nat.floor_lt (by positivity), Nat.le_floor_iff (by positivity), lt_div_iff₀ hd,
      div_le_iff₀ hd]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  -- pointwise bound
  have hpt : ∀ n ∈ range (k + 1), |f n * w N k n - (if n ∈ Ioc A B then f n else 0)| ≤
      |(N : ℝ) - k| / dd N * f n + (if n ∈ E then f n else 0) := by
    intro n hn
    have hw0 := w_nonneg N k n
    have hw1 := w_le_one hN k n
    have hq : 0 ≤ |(N : ℝ) - k| / dd N := by positivity
    by_cases hin : n ∈ Ioc A B
    · rw [if_pos hin]
      obtain ⟨h1, h2⟩ := (hmemD n).mp hin
      have hge := w_ge hN k n h1.le h2
      have : |f n * w N k n - f n| = f n * (1 - w N k n) := by
        rw [show f n * w N k n - f n = -(f n * (1 - w N k n)) by ring, abs_neg,
          abs_of_nonneg (mul_nonneg (hf0 n) (by linarith))]
      rw [this]
      have : f n * (1 - w N k n) ≤ |(N : ℝ) - k| / dd N * f n := by nlinarith [hf0 n]
      have : (0 : ℝ) ≤ (if n ∈ E then f n else 0) := by split_ifs <;> simp [hf0 n]
      linarith
    · rw [if_neg hin, sub_zero, abs_of_nonneg (mul_nonneg (hf0 n) hw0)]
      have h0 : 0 ≤ |(N : ℝ) - k| / dd N * f n := mul_nonneg hq (hf0 n)
      by_cases hedge : aa N < (n : ℝ) / dd N ∧ (n : ℝ) / dd N < bb N + 1
      · have hnE : n ∈ E := by
          simp only [hE, Finset.mem_filter]; exact ⟨hn, hedge.1, hedge.2, hin⟩
        rw [if_pos hnE]
        nlinarith [hf0 n]
      · have : w N k n = 0 := by
          apply w_eq_zero hN
          by_contra hc; push Not at hc; exact hedge ⟨hc.1, hc.2⟩
        rw [this, mul_zero]
        have : (0 : ℝ) ≤ (if n ∈ E then f n else 0) := by split_ifs <;> simp [hf0 n]
        linarith
  -- sum the pointwise bound
  have hsum : |Dt N k - DLu N k| ≤
      |(N : ℝ) - k| / dd N * ∑ n ∈ range (k + 1), f n + ∑ n ∈ E, f n := by
    rw [Dt_eq hN, hD, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hE, Finset.sum_filter]
    have : ∀ n : ℕ, n ∈ range (k + 1) → (if n ∈ E then f n else 0) =
        if (aa N < (n : ℝ) / dd N ∧ (n : ℝ) / dd N < bb N + 1 ∧ n ∉ Ioc A B) then f n else 0 := by
      intro n hn
      simp only [hE, Finset.mem_filter, hn, true_and]
    rw [Finset.sum_congr rfl this]
  -- the full sum and the edge sum
  have hfull : ∑ n ∈ range (k + 1), f n ≤ (k + 1) * Real.log k ^ 2 := by
    have := Finset.sum_le_sum (fun n (_ : n ∈ range (k + 1)) => term_le k n)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    push_cast at this; linarith
  have hEsub : E ⊆ Ioc ⌊aa N * dd N⌋₊ ⌊aa N * dd N + dd N⌋₊ ∪
      Ioc ⌊bb N * dd N⌋₊ ⌊bb N * dd N + dd N⌋₊ := by
    intro n hn
    simp only [hE, Finset.mem_filter] at hn
    obtain ⟨_, h1, h2, h3⟩ := hn
    rw [hmemD] at h3
    rw [lt_div_iff₀ hd] at h1
    rw [div_lt_iff₀ hd] at h2
    simp only [Finset.mem_union, Finset.mem_Ioc]
    rw [Nat.floor_lt (by positivity), Nat.floor_lt (by positivity),
      Nat.le_floor_iff (by positivity), Nat.le_floor_iff (by positivity)]
    by_cases hc : (n : ℝ) / dd N ≤ aa N + 1
    · left; rw [div_le_iff₀ hd] at hc; constructor <;> linarith
    · right
      push Not at hc
      have hb : bb N < (n : ℝ) / dd N := by
        by_contra hh; push Not at hh; exact h3 ⟨hc, hh⟩
      rw [lt_div_iff₀ hd] at hb
      constructor <;> linarith
  have hEcard : (E.card : ℝ) ≤ 2 * dd N + 2 := by
    have h := Finset.card_le_card hEsub
    have h2 := Finset.card_union_le (Ioc ⌊aa N * dd N⌋₊ ⌊aa N * dd N + dd N⌋₊)
      (Ioc ⌊bb N * dd N⌋₊ ⌊bb N * dd N + dd N⌋₊)
    have c1 := card_Ioc_floor_le (x := aa N * dd N) (y := aa N * dd N + dd N) (by positivity)
      (by linarith)
    have c2 := card_Ioc_floor_le (x := bb N * dd N) (y := bb N * dd N + dd N) (by positivity)
      (by linarith)
    have : (E.card : ℝ) ≤ ((Ioc ⌊aa N * dd N⌋₊ ⌊aa N * dd N + dd N⌋₊).card : ℝ) +
        ((Ioc ⌊bb N * dd N⌋₊ ⌊bb N * dd N + dd N⌋₊).card : ℝ) := by
      exact_mod_cast h.trans h2
    linarith
  have hedge : ∑ n ∈ E, f n ≤ (2 * dd N + 2) * Real.log k ^ 2 := by
    have := Finset.sum_le_sum (fun n (_ : n ∈ E) => term_le k n)
    simp only [Finset.sum_const, nsmul_eq_mul] at this
    have hl : 0 ≤ Real.log k ^ 2 := sq_nonneg _
    nlinarith
  have hq : 0 ≤ |(N : ℝ) - k| / dd N := by positivity
  have := mul_le_mul_of_nonneg_left hfull hq
  linarith

/-- On the window, `|Dt - D| ≤ N^{0.99995}` for every large `N`. -/
theorem lemma1_eventually : ∃ N1 : ℕ, ∀ N, N1 ≤ N → ∀ k ∈ Win N,
    |Dt N k - DLu N k| ≤ (N : ℝ) ^ (1 - 0.00005 : ℝ) := by
  have hlo := (isLittleO_log_rpow_atTop (r := 0.000025) (by norm_num)).bound
    (c := 1 / 4) (by norm_num)
  have h2 : Tendsto (fun N : ℕ => (2 : ℝ) * N) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp (h2.eventually hlo)
  refine ⟨max N1 1, fun N hN k hk => ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hN)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hd := dd_pos hNpos
  have hl := hN1 N (le_trans (le_max_left _ _) hN)
  have hx1 : (1 : ℝ) ≤ 2 * N := by linarith
  rw [Real.norm_of_nonneg (Real.log_nonneg hx1),
    Real.norm_of_nonneg (rpow_nonneg (by linarith) _)] at hl
  have hstep := lemma1_step N k hNpos
  simp only [Win, Finset.mem_Icc] at hk
  have hrad := rad_le N
  have hk2 : k ≤ 2 * N := by omega
  have hkr : (k : ℝ) ≤ 2 * N := by exact_mod_cast hk2
  -- |N - k| ≤ N^{0.99979}
  have hNk : |(N : ℝ) - k| ≤ (N : ℝ) ^ (0.99979 : ℝ) := by
    have hr : (rad N : ℝ) ≤ (N : ℝ) ^ (0.99979 : ℝ) := by
      unfold rad; rw [rad_eq N hNpos]; exact Nat.floor_le (by positivity)
    have : |(N : ℝ) - k| ≤ rad N := by
      rw [abs_le]; constructor
      · have : k ≤ N + rad N := hk.2
        have : (k : ℝ) ≤ N + rad N := by exact_mod_cast this
        linarith
      · have : N - rad N ≤ k := hk.1
        have : (N : ℝ) ≤ k + rad N := by exact_mod_cast (show N ≤ k + rad N by omega)
        linarith
    linarith
  -- log k ≤ log 2N ≤ (2N)^{0.000025}/4
  have hlogk : Real.log k ^ 2 ≤ (N : ℝ) ^ (0.00005 : ℝ) / 8 := by
    have hlk0 : 0 ≤ Real.log k := Real.log_natCast_nonneg k
    have hlk : Real.log k ≤ Real.log (2 * N) := by
      rcases Nat.eq_zero_or_pos k with h0 | hkp
      · subst h0; simp; exact Real.log_nonneg hx1
      · exact Real.log_le_log (by exact_mod_cast hkp) hkr
    have hsq : Real.log k ^ 2 ≤ ((1 / 4) * (2 * (N : ℝ)) ^ (0.000025 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hlk0 (hlk.trans hl) 2
    have hpw : ((2 * (N : ℝ)) ^ (0.000025 : ℝ)) ^ 2 = (2 : ℝ) ^ (0.00005 : ℝ) * (N : ℝ) ^ (0.00005 : ℝ) := by
      rw [← rpow_natCast, ← rpow_mul (by positivity), mul_rpow (by norm_num) hN'.le]; norm_num
    have h2p : (2 : ℝ) ^ (0.00005 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (0.00005 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := rpow_one 2
    have hNp : 0 ≤ (N : ℝ) ^ (0.00005 : ℝ) := by positivity
    calc Real.log k ^ 2 ≤ _ := hsq
      _ = (1 / 16) * (((2 * (N : ℝ)) ^ (0.000025 : ℝ)) ^ 2) := by ring
      _ = (1 / 16) * ((2 : ℝ) ^ (0.00005 : ℝ) * (N : ℝ) ^ (0.00005 : ℝ)) := by rw [hpw]
      _ ≤ (1 / 16) * (2 * (N : ℝ) ^ (0.00005 : ℝ)) := by gcongr
      _ = (N : ℝ) ^ (0.00005 : ℝ) / 8 := by ring
  -- the two coefficients are at most 7 N^{0.9999}
  have hdd : dd N = (N : ℝ) ^ (0.9999 : ℝ) := rfl
  have hc1 : |(N : ℝ) - k| / dd N * (k + 1) ≤ 3 * (N : ℝ) ^ (0.9999 : ℝ) := by
    have hq : |(N : ℝ) - k| / dd N ≤ (N : ℝ) ^ (-0.00011 : ℝ) := by
      rw [div_le_iff₀ hd, hdd, ← rpow_add hN']
      have : (-0.00011 : ℝ) + 0.9999 = 0.99979 := by norm_num
      rw [this]; exact hNk
    have hk1 : (k : ℝ) + 1 ≤ 3 * N := by linarith
    have hneg : 0 ≤ (N : ℝ) ^ (-0.00011 : ℝ) := by positivity
    calc |(N : ℝ) - k| / dd N * (k + 1) ≤ (N : ℝ) ^ (-0.00011 : ℝ) * (3 * N) :=
          mul_le_mul hq hk1 (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1) hneg
      _ = 3 * ((N : ℝ) ^ (-0.00011 : ℝ) * (N : ℝ) ^ (1 : ℝ)) := by rw [rpow_one]; ring
      _ = 3 * (N : ℝ) ^ (0.99989 : ℝ) := by rw [← rpow_add hN']; norm_num
      _ ≤ 3 * (N : ℝ) ^ (0.9999 : ℝ) := by
          have := rpow_le_rpow_of_exponent_le hN1r (show (0.99989 : ℝ) ≤ 0.9999 by norm_num)
          linarith
  have hc2 : 2 * dd N + 2 ≤ 4 * (N : ℝ) ^ (0.9999 : ℝ) := by
    have : (1 : ℝ) ≤ (N : ℝ) ^ (0.9999 : ℝ) := Real.one_le_rpow hN1r (by norm_num)
    rw [hdd]; linarith
  have hL0 : 0 ≤ Real.log k ^ 2 := sq_nonneg _
  have hbound : |Dt N k - DLu N k| ≤ 7 * (N : ℝ) ^ (0.9999 : ℝ) * Real.log k ^ 2 := by
    have e1 : |(N : ℝ) - k| / dd N * ((k + 1) * Real.log k ^ 2) =
        (|(N : ℝ) - k| / dd N * (k + 1)) * Real.log k ^ 2 := by ring
    rw [e1] at hstep
    nlinarith
  have hP : 0 ≤ (N : ℝ) ^ (0.9999 : ℝ) := by positivity
  calc |Dt N k - DLu N k| ≤ 7 * (N : ℝ) ^ (0.9999 : ℝ) * Real.log k ^ 2 := hbound
    _ ≤ 7 * (N : ℝ) ^ (0.9999 : ℝ) * ((N : ℝ) ^ (0.00005 : ℝ) / 8) := by gcongr
    _ ≤ (N : ℝ) ^ (0.9999 : ℝ) * (N : ℝ) ^ (0.00005 : ℝ) := by
        have : 0 ≤ (N : ℝ) ^ (0.9999 : ℝ) * (N : ℝ) ^ (0.00005 : ℝ) := by positivity
        nlinarith
    _ = (N : ℝ) ^ (1 - 0.00005 : ℝ) := by rw [← rpow_add hN']; norm_num

/-! ### The input bundle with Lemma 1 PROVED -/

/-- **Cited input**, as `Inputs` but with Lemma 1 replaced by its first step only: the
orthogonality identity `D̃(k) = Dt(k)` of p. 2362 with (9), `Dt(k) = D₁(k) + D₂(k)`, exact. -/
structure InputsT where
  D1 : ℕ → ℕ → ℝ
  D2 : ℕ → ℕ → ℂ
  D6 : ℕ → ℕ → ℂ
  S : ℕ → ℝ
  S_ge : ∀ k, Even k → 1 ≤ S k
  N0 : ℕ
  Cerr : ℝ
  c1 : ℝ
  c1_pos : 0 < c1
  C9 : ℝ
  C86 : ℝ
  orth9 : ∀ N, N0 ≤ N → ∀ k ∈ Win N, (Dt N k : ℂ) = (D1 N k : ℂ) + D2 N k
  lower : ∀ N, N0 ≤ N →
    (∀ k ∈ Win N, Even k →
      S k * (bb N - aa N) * dd N *
        ((Real.log (Real.log (Real.log N)))⁻¹ - Cerr * (Real.log (Real.log N)) ^ (-(1 / 2) : ℝ))
        - ‖D6 N k‖ < D1 N k) ∨
    (∀ k ∈ Win N, Even k →
      S k * (bb N - aa N) * dd N * c1 * PP N ^ (-0.00001 : ℝ) * Real.log (PP N) *
        (2 * c⁻¹ - Cerr * (Real.log (Real.log (Real.log N))) ^ (-0.1 : ℝ))
        - ‖D6 N k‖ ≤ D1 N k)
  sec9 : ∀ N, N0 ≤ N → ∑ k ∈ Win N, ‖D2 N k‖ ^ 2 ≤ C9 * (N : ℝ) ^ (3 - c + 0.00011)
  eq86 : ∀ N, N0 ≤ N →
    ∑ k ∈ Win N, ‖D6 N k‖ ^ 2 ≤ C86 * PP N ^ (-1 : ℝ) * dd N * (N : ℝ) ^ (2.0003 : ℝ)

/-- With the second step of Lemma 1 PROVED, `InputsT` gives `Inputs`. -/
noncomputable def InputsT.toInputs (J : InputsT) : Inputs :=
  have hex := lemma1_eventually
  { D1 := J.D1, D2 := J.D2, D6 := J.D6, S := J.S, S_ge := J.S_ge,
    N0 := max J.N0 hex.choose, C1 := 1, Cerr := J.Cerr, c1 := J.c1, c1_pos := J.c1_pos,
    C9 := J.C9, C86 := J.C86
    lemma1 := fun N hN k hk => by
      have h1 := hex.choose_spec N (le_trans (le_max_right _ _) hN) k hk
      have h2 := J.orth9 N (le_trans (le_max_left _ _) hN) k hk
      rw [← h2, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, one_mul]
      exact h1
    lower := fun N hN => J.lower N (le_trans (le_max_left _ _) hN)
    sec9 := fun N hN => J.sec9 N (le_trans (le_max_left _ _) hN)
    eq86 := fun N hN => J.eq86 N (le_trans (le_max_left _ _) hN) }

/-- CONDITIONAL ON `InputsT`: the paper's Theorem `E(x) ≪ x^{0.879}`. -/
theorem lu_of_inputsT (J : InputsT) : PowerBound 0.879 := lu_of_inputs J.toInputs

/-- CONDITIONAL ON `InputsT`: `E X ≪ X^{0.8789126}`. -/
theorem lu_sharp_of_inputsT (J : InputsT) : PowerBound θ := lu_sharp_of_inputs J.toInputs

/-- CONDITIONAL ON `InputsT`: Pintz's eventual form `E X < X^{0.879}`. -/
theorem lu_eventually_of_inputsT (J : InputsT) : Lu2010.lu_eventually_stmt :=
  lu_eventually_of_inputs J.toInputs

end LeanLab.ExceptionalSet.Lu2010Lemma1

#print axioms LeanLab.ExceptionalSet.Lu2010Lemma1.tset_eq
#print axioms LeanLab.ExceptionalSet.Lu2010Lemma1.tset_measurable
#print axioms LeanLab.ExceptionalSet.Lu2010Lemma1.Dt_eq
#print axioms LeanLab.ExceptionalSet.Lu2010Lemma1.w_nonneg
#print axioms LeanLab.ExceptionalSet.Lu2010Lemma1.w_le_one
#print axioms LeanLab.ExceptionalSet.Lu2010Lemma1.w_eq_zero
#print axioms LeanLab.ExceptionalSet.Lu2010Lemma1.w_ge
#print axioms LeanLab.ExceptionalSet.Lu2010Lemma1.term_le
#print axioms LeanLab.ExceptionalSet.Lu2010Lemma1.card_Ioc_floor_le
#print axioms LeanLab.ExceptionalSet.Lu2010Lemma1.lemma1_step
#print axioms LeanLab.ExceptionalSet.Lu2010Lemma1.lemma1_eventually
#print axioms LeanLab.ExceptionalSet.Lu2010Lemma1.InputsT.toInputs
#print axioms LeanLab.ExceptionalSet.Lu2010Lemma1.lu_of_inputsT
#print axioms LeanLab.ExceptionalSet.Lu2010Lemma1.lu_sharp_of_inputsT
#print axioms LeanLab.ExceptionalSet.Lu2010Lemma1.lu_eventually_of_inputsT
