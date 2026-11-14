import LeanLab.ExceptionalSet.Decomp371a
import LeanLab.ExceptionalSet.PhaseInterval446
import LeanLab.ExceptionalSet.UpJ200.Decomp450e

/-!
P0082 pages354 and359, Theorem2 and Lemma4, and page364 before Lemma8.
Finite Fourier counting for the outer upper boundary pieces.
The missing interval majorant is isolated from all elementary counting steps.
No import uses SPLIT_leaf_boundary_outer_high.
Source: https://doi.org/10.5802/aif.1621
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp524a

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE eC)
open LeanLab.ExceptionalSet.DecompJ200 (window)


/-- LEAF. P0082 page359 Lemma4, the unnumbered counting display and the
omitted Vinogradov argument. This is the finite Fourier majorant input,
not the discrepancy conclusion. Its coefficients absorb both signed frequencies.
The constant four is a relaxed majorant constant, not a printed constant.
No decay assumption occurs here. The degrees at most three are proved below.
Akiyama and Tanigawa page332 displays4 to7 provide the Selberg construction.
Source: https://doi.org/10.5486/PMD.2004.2888 -/
theorem leaf_interval_majorant524 (a b : ℝ) (hab : a < b)
    (ha : 0 ≤ a) (hb : b ≤ 1) (H : ℕ) :
    ∃ c₀ : ℝ, ∃ c : ℕ → ℂ,
      c₀ ≤ b - a + 4 / ((H : ℝ) + 1) ∧
      (∀ h ∈ Icc 1 H, ‖c h‖ ≤ 4 / (h : ℝ)) ∧
      ∀ x : ℝ, (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
        c₀ + (∑ h ∈ Icc 1 H, c h * eC ((h : ℝ) * x)).re := by
  classical
  by_cases hH : H ≤ 3
  · refine ⟨1, fun _ => 0, ?_, ?_, ?_⟩
    · have hd : (0 : ℝ) < (H : ℝ) + 1 := by positivity
      have hH3 : (H : ℝ) ≤ 3 := by exact_mod_cast hH
      have hr : (1 : ℝ) ≤ 4 / ((H : ℝ) + 1) := (le_div_iff₀ hd).mpr (by linarith)
      linarith
    · intro h hh
      simpa only [norm_zero] using
        (div_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Nat.cast_nonneg h))
    · intro x
      simp only [zero_mul, Finset.sum_const_zero, Complex.zero_re, add_zero]
      split_ifs <;> norm_num
  · sorry

/-- P0082 page359 Lemma4, unnumbered display. Summing a Fourier
majorant reduces the interval count to its constant term and harmonic sums.
CONDITIONAL ON the supplied finite majorant. -/
theorem count_of_majorant524 (s : Finset ℕ) (f : ℕ → ℝ) (a b c₀ : ℝ)
    (H : ℕ) (c : ℕ → ℂ)
    (hc₀ : c₀ ≤ b - a + 4 / ((H : ℝ) + 1))
    (hc : ∀ h ∈ Icc 1 H, ‖c h‖ ≤ 4 / (h : ℝ))
    (hm : ∀ x : ℝ,
      (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
        c₀ + (∑ h ∈ Icc 1 H, c h * eC ((h : ℝ) * x)).re) :
    ((s.filter (fun n => a ≤ Int.fract (f n) ∧ Int.fract (f n) < b)).card : ℝ) ≤
      (b - a + 4 / ((H : ℝ) + 1)) * s.card +
        ∑ h ∈ Icc 1 H, (4 / (h : ℝ)) * ‖∑ n ∈ s, eC ((h : ℝ) * f n)‖ := by
  classical
  have hsum : ((s.filter (fun n => a ≤ Int.fract (f n) ∧ Int.fract (f n) < b)).card : ℝ) ≤
      ∑ n ∈ s, (c₀ + (∑ h ∈ Icc 1 H, c h * eC ((h : ℝ) * f n)).re) := by
    calc
      _ = ∑ n ∈ s, (if a ≤ Int.fract (f n) ∧ Int.fract (f n) < b then (1 : ℝ) else 0) := by
        simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ _ := Finset.sum_le_sum fun n _ => hm (f n)
  have heq : (∑ n ∈ s, (c₀ + (∑ h ∈ Icc 1 H, c h * eC ((h : ℝ) * f n)).re)) =
      c₀ * s.card + (∑ h ∈ Icc 1 H, c h * ∑ n ∈ s, eC ((h : ℝ) * f n)).re := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [mul_comm (s.card : ℝ), ← Complex.re_sum, Finset.sum_comm]
    congr 2
    apply Finset.sum_congr rfl
    intro h _
    exact (Finset.mul_sum _ _ _).symm
  rw [heq] at hsum
  refine hsum.trans (add_le_add (mul_le_mul_of_nonneg_right hc₀ (Nat.cast_nonneg _)) ?_)
  rw [Complex.re_sum]
  apply Finset.sum_le_sum
  intro h hh
  calc
    _ ≤ ‖c h * ∑ n ∈ s, eC ((h : ℝ) * f n)‖ := Complex.re_le_norm _
    _ = ‖c h‖ * ‖∑ n ∈ s, eC ((h : ℝ) * f n)‖ := norm_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (hc h hh) (norm_nonneg _)

/-- P0082 page359 Lemma4. The harmonic sum has at most H terms.
Bounding every integer frequency by Q costs at most 4 H Q. -/
theorem harmonic_sum_bound524 (f : ℕ → ℂ) (H : ℕ) (Q : ℝ) (hQ : 0 ≤ Q)
    (hf : ∀ h ∈ Icc 1 H, ‖f h‖ ≤ Q) :
    (∑ h ∈ Icc 1 H, (4 / (h : ℝ)) * ‖f h‖) ≤ 4 * H * Q := by
  calc
    _ ≤ ∑ h ∈ Icc 1 H, 4 * Q := by
      apply Finset.sum_le_sum
      intro h hh
      have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (Finset.mem_Icc.mp hh).1
      have hdiv : (4 : ℝ) / h ≤ 4 := (div_le_iff₀ (by linarith)).mpr (by linarith)
      exact mul_le_mul hdiv (hf h hh) (norm_nonneg _) (by norm_num)
    _ = _ := by simp [Nat.card_Icc]; ring

/-- P0082 page359 Lemma4. The exponential cutoff is positive and lies
between exp t and 2 exp t for nonnegative t. -/
theorem cutoff_bounds524 (t : ℝ) (ht : 0 ≤ t) :
    1 ≤ Nat.ceil (Real.exp t) ∧
      Real.exp t ≤ (Nat.ceil (Real.exp t) : ℝ) ∧
      (Nat.ceil (Real.exp t) : ℝ) ≤ 2 * Real.exp t := by
  have he : 1 ≤ Real.exp t := Real.one_le_exp ht
  refine ⟨Nat.one_le_ceil_iff.mpr (Real.exp_pos _), Nat.le_ceil _, ?_⟩
  have hc := Nat.ceil_lt_add_one (Real.exp_pos t).le
  linarith

/-- P0082 page359 Lemma4. The reciprocal cutoff error is at most
exp minus t. This avoids a logarithmic cutoff that is too small for the target. -/
theorem cutoff_reciprocal524 (t : ℝ) (ht : 0 ≤ t) :
    1 / ((Nat.ceil (Real.exp t) : ℝ) + 1) ≤ Real.exp (-t) := by
  have hc := (cutoff_bounds524 t ht).2.1
  have hp := Real.exp_pos t
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le hp
    (by linarith : Real.exp t ≤ (Nat.ceil (Real.exp t) : ℝ) + 1)

/-- P0082 page359 Lemma4. Multiplying the cutoff by the frequency
error still leaves the required boundary decay when kappa is at most eta. -/
theorem cutoff_decay524 (κ η u : ℝ) (hκ : 0 ≤ κ) (hη : κ ≤ η) (hu : 0 ≤ u) :
    (Nat.ceil (Real.exp (κ / 8 * u)) : ℝ) * Real.exp (-η * u) ≤
      2 * Real.exp (-(κ / 8 * u)) := by
  calc
    _ ≤ (2 * Real.exp (κ / 8 * u)) * Real.exp (-η * u) :=
      mul_le_mul_of_nonneg_right (cutoff_bounds524 _ (by positivity)).2.2
        (Real.exp_pos _).le
    _ = 2 * Real.exp (κ / 8 * u - η * u) := by rw [mul_assoc, ← Real.exp_add]; congr 2 <;> ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
      have hm := mul_le_mul_of_nonneg_right hη hu
      have hku := mul_nonneg hκ hu
      nlinarith

/-- P0082 pages354 and359. Every cutoff frequency eventually lies
below F of N to the power C. The threshold is uniform for kappa at most one. -/
theorem cutoff_frequency_range524 (γ C : ℝ) (hγ : 1 < γ) (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ κ : ℝ, 0 ≤ κ → κ ≤ 1 →
      (Nat.ceil (Real.exp (κ / 8 * Real.log N ^ (3 - 2 * γ))) : ℝ) ≤ F γ N ^ C := by
  have hl : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp := (tendsto_rpow_atTop (by linarith : 0 < γ - 1)).comp hl
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hl.eventually_ge_atTop 1)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (hp.eventually_ge_atTop (2 / C))
  refine ⟨max N₁ N₂, fun N hN κ hκ hκ1 => ?_⟩
  have hL : 1 ≤ Real.log (N : ℝ) := hN₁ N ((le_max_left _ _).trans hN)
  have hpow : 2 / C ≤ Real.log (N : ℝ) ^ (γ - 1) :=
    hN₂ N ((le_max_right _ _).trans hN)
  have hLpos : 0 < Real.log (N : ℝ) := by linarith
  have hpL : Real.log (N : ℝ) ^ (3 - 2 * γ) ≤ Real.log (N : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL (show 3 - 2 * γ ≤ 1 by linarith)
  have hsplit : Real.log (N : ℝ) ^ γ =
      Real.log (N : ℝ) * Real.log (N : ℝ) ^ (γ - 1) := by
    calc
      _ = Real.log (N : ℝ) ^ (1 + (γ - 1)) := by congr 1; ring
      _ = Real.log (N : ℝ) ^ (1 : ℝ) * Real.log (N : ℝ) ^ (γ - 1) := Real.rpow_add hLpos _ _
      _ = _ := by rw [Real.rpow_one]
  have hlarge : 2 * Real.log (N : ℝ) ≤ C * Real.log (N : ℝ) ^ γ := by
    rw [hsplit]
    have hh := (div_le_iff₀ hC).mp hpow
    nlinarith
  have hu : 0 ≤ Real.log (N : ℝ) ^ (3 - 2 * γ) := Real.rpow_nonneg hLpos.le _
  have ht : κ / 8 * Real.log (N : ℝ) ^ (3 - 2 * γ) + 1 ≤ C * Real.log (N : ℝ) ^ γ := by
    have hm := mul_le_mul_of_nonneg_right hκ1 hu
    nlinarith
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  calc
    _ ≤ 2 * Real.exp (κ / 8 * Real.log (N : ℝ) ^ (3 - 2 * γ)) :=
      (cutoff_bounds524 _ (by positivity)).2.2
    _ ≤ Real.exp 1 * Real.exp (κ / 8 * Real.log (N : ℝ) ^ (3 - 2 * γ)) :=
      mul_le_mul_of_nonneg_right he1 (Real.exp_pos _).le
    _ = Real.exp (κ / 8 * Real.log (N : ℝ) ^ (3 - 2 * γ) + 1) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (C * Real.log (N : ℝ) ^ γ) := Real.exp_le_exp.mpr ht
    _ = F γ N ^ C := by rw [F, ← Real.exp_mul]; congr 1; ring

/-- P0082 page359 Lemma4 and page364 display23. A short interval
count follows from its Fourier majorant and the integer frequency decay.
CONDITIONAL ON these two supplied inputs. All cutoff errors are explicit. -/
theorem interval_count_of_decay524 (s : Finset ℕ) (f : ℕ → ℝ) (N : ℕ)
    (a b κ η u B : ℝ) (hκ : 0 ≤ κ) (hη : κ ≤ η) (hu : 0 ≤ u) (hB : 0 ≤ B)
    (hcard : (s.card : ℝ) ≤ N) (hlen : b - a ≤ Real.exp (-(κ / 8 * u)))
    (hlen0 : 0 ≤ b - a)
    (hmajor : ∃ c₀ : ℝ, ∃ c : ℕ → ℂ,
      c₀ ≤ b - a + 4 / ((Nat.ceil (Real.exp (κ / 8 * u)) : ℝ) + 1) ∧
      (∀ h ∈ Icc 1 (Nat.ceil (Real.exp (κ / 8 * u))), ‖c h‖ ≤ 4 / (h : ℝ)) ∧
      ∀ x : ℝ, (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
        c₀ + (∑ h ∈ Icc 1 (Nat.ceil (Real.exp (κ / 8 * u))), c h * eC ((h : ℝ) * x)).re)
    (hsum : ∀ h ∈ Icc 1 (Nat.ceil (Real.exp (κ / 8 * u))),
      ‖∑ n ∈ s, eC ((h : ℝ) * f n)‖ ≤ B * N * Real.exp (-η * u)) :
    ((s.filter (fun n => a ≤ Int.fract (f n) ∧ Int.fract (f n) < b)).card : ℝ) ≤
      (5 + 8 * B) * N * Real.exp (-(κ / 8 * u)) := by
  obtain ⟨c₀, c, hc₀, hc, hm⟩ := hmajor
  have hcount := count_of_majorant524 s f a b c₀ _ c hc₀ hc hm
  have hrecip := cutoff_reciprocal524 (κ / 8 * u) (by positivity)
  have hdecay := cutoff_decay524 κ η u hκ hη hu
  have hcoef : b - a + 4 / ((Nat.ceil (Real.exp (κ / 8 * u)) : ℝ) + 1) ≤
      5 * Real.exp (-(κ / 8 * u)) := by
    have hh := mul_le_mul_of_nonneg_left hrecip (by norm_num : (0 : ℝ) ≤ 4)
    simp only [mul_one_div] at hh
    linarith
  have hcoef0 : 0 ≤ b - a + 4 / ((Nat.ceil (Real.exp (κ / 8 * u)) : ℝ) + 1) := by positivity
  have hfirst : (b - a + 4 / ((Nat.ceil (Real.exp (κ / 8 * u)) : ℝ) + 1)) * s.card ≤
      5 * Real.exp (-(κ / 8 * u)) * N := by
    exact mul_le_mul hcoef hcard (Nat.cast_nonneg _) (by positivity)
  have hsum' := harmonic_sum_bound524
    (fun h => ∑ n ∈ s, eC ((h : ℝ) * f n)) _
    (B * N * Real.exp (-η * u)) (by positivity) hsum
  have hsecond : 4 * (Nat.ceil (Real.exp (κ / 8 * u)) : ℝ) *
      (B * N * Real.exp (-η * u)) ≤ 8 * B * N * Real.exp (-(κ / 8 * u)) := by
    calc
      _ = 4 * B * N * ((Nat.ceil (Real.exp (κ / 8 * u)) : ℝ) * Real.exp (-η * u)) := by ring
      _ ≤ 4 * B * N * (2 * Real.exp (-(κ / 8 * u))) :=
        mul_le_mul_of_nonneg_left hdecay (by positivity)
      _ = _ := by ring
  calc
    _ ≤ _ := hcount
    _ ≤ 5 * Real.exp (-(κ / 8 * u)) * N +
        8 * B * N * Real.exp (-(κ / 8 * u)) := add_le_add hfirst (hsum'.trans hsecond)
    _ = _ := by ring

/-- P0082 page365 Lemma8 width. The exponential and real power
forms of the boundary scale agree exactly. -/
theorem boundary_scale524 (γ κ : ℝ) (N : ℕ) :
    calE γ κ N ^ (-(1 / 8 : ℝ)) =
      Real.exp (-(κ / 8 * Real.log N ^ (3 - 2 * γ))) := by
  unfold calE
  rw [← Real.exp_mul]
  congr 1
  ring



/-- P0082 page359 Lemma4, derived cutoff diagnostic. A cutoff only
linear in log N cannot absorb the required subexponential scale.
This is a statement about the proposed proof bookkeeping, not a paper error. -/
theorem logarithmic_cutoff_too_small524 (p κ B : ℝ) (hp : 0 < p) (hκ : 0 < κ) :
    ∃ L : ℝ, 1 ≤ L ∧ B * Real.exp (-κ * L ^ p) < 1 / ((Nat.ceil L : ℝ) + 1) := by
  obtain ⟨U, hU⟩ := Filter.eventually_atTop.mp
    ((tendsto_exp_mul_div_rpow_atTop (1 / p) κ hκ).eventually_ge_atTop (3 * (|B| + 1)))
  let u := max 1 U
  have hu1 : 1 ≤ u := le_max_left _ _
  have hu : 0 < u := by linarith
  let L := u ^ (1 / p)
  have hL : 1 ≤ L := Real.one_le_rpow hu1 (by positivity)
  have hLp : L ^ p = u := by
    dsimp [L]
    rw [← Real.rpow_mul hu.le]
    have he : 1 / p * p = 1 := by field_simp
    rw [he, Real.rpow_one]
  have hexp : 3 * (|B| + 1) * L ≤ Real.exp (κ * u) :=
    (le_div_iff₀ (by dsimp [L]; positivity)).mp (hU u (le_max_right _ _))
  have hceil : (Nat.ceil L : ℝ) + 1 ≤ 3 * L := by
    have hc := Nat.ceil_lt_add_one (by linarith : 0 ≤ L)
    linarith
  have hd : 0 < (Nat.ceil L : ℝ) + 1 := by positivity
  have hB : B * ((Nat.ceil L : ℝ) + 1) < Real.exp (κ * u) := by
    calc
      _ ≤ |B| * ((Nat.ceil L : ℝ) + 1) := mul_le_mul_of_nonneg_right (le_abs_self B) hd.le
      _ ≤ |B| * (3 * L) := mul_le_mul_of_nonneg_left hceil (abs_nonneg _)
      _ < 3 * (|B| + 1) * L := by nlinarith
      _ ≤ _ := hexp
  refine ⟨L, hL, ?_⟩
  rw [hLp, show -κ * u = -(κ * u) by ring, Real.exp_neg, ← div_eq_mul_inv]
  apply (div_lt_div_iff₀ (Real.exp_pos _) hd).mpr
  simpa only [one_mul] using hB

/-- P0082 page354 Theorem2, specialized to positive integer frequencies
on the half index interval used in page359 Lemma4. Endpoint rounding
and the change of exponential scale are elementary and supplied explicitly.
CONDITIONAL ON the supplied Theorem2 statement. -/
theorem integer_frequency_decay524 (hT : U1539.Theorem2)
    (γ δ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (hδ : 0 < δ)
    (hδsmall : δ < min ((γ - 1) / 24) (1 / 12)) :
    ∃ η B : ℝ, 0 < η ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ h : ℕ, 1 ≤ h → (h : ℝ) ≤ F γ N ^ (6 * δ) →
        ‖∑ n ∈ Ioc (N / 2) N, eC ((h : ℝ) * F γ n)‖ ≤
          B * N * Real.exp (-η * Real.log N ^ (3 - 2 * γ)) := by
  have hδγ : δ < (γ - 1) / 24 := hδsmall.trans_le (min_le_left _ _)
  have hδ12 : δ < 1 / 12 := hδsmall.trans_le (min_le_right _ _)
  obtain ⟨η, B, hη, hs⟩ := hT γ h1 h2 (1 - 2 * δ) (12 * δ)
    (by linarith) (by linarith) (by positivity) (by linarith)
  obtain ⟨Nr, hr⟩ := UpJ200.Decomp450e.frequency_range_supplied γ δ h1 h2 hδ hδsmall
  obtain ⟨A, hA, Nd, hd⟩ := UpJ200.Decomp450c.decay_rescale_supplied γ η (|B| + 1)
    h1 h2 hη (by positivity)
  refine ⟨η / 4, A, by positivity, hA, max 4 (max Nr Nd), fun N hN h hh1 hhF => ?_⟩
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNr : Nr ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNd : Nd ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hh1r : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hF1 : 1 < F γ N := by
    rw [F]
    exact Real.one_lt_exp_iff.mpr (Real.rpow_pos_of_pos hL _)
  have hlo : F γ N ^ (3 * δ - 1) < |(h : ℝ)| := by
    rw [abs_of_nonneg (Nat.cast_nonneg h)]
    exact (Real.rpow_lt_one_of_one_lt_of_neg hF1 (by linarith : 3 * δ - 1 < 0)).trans_le hh1r
  have hhi : |(h : ℝ)| ≤ 2 * F γ N ^ (6 * δ) := by
    rw [abs_of_nonneg (Nat.cast_nonneg h)]
    have hp : 0 ≤ F γ N ^ (6 * δ) := Real.rpow_nonneg (Real.exp_pos _).le _
    linarith
  obtain ⟨hl, hu⟩ := hr N hNr (h : ℝ) hlo hhi
  have hraw := hs (N / 2) (by omega) (h : ℝ) hl hu
  have hsum : ‖U1539.expSumF γ (h : ℝ) (N / 2)‖ ≤
      (|B| + 1) * (N / 2 : ℕ) * Real.exp (-η * Real.log (N / 2 : ℕ) ^ (3 - 2 * γ)) := by
    refine hraw.trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact (le_abs_self B).trans (by linarith)
  have hphase : ‖∑ n ∈ Ioc (N / 2) N, eC ((h : ℝ) * F γ n)‖ ≤
      ‖U1539.expSumF γ (h : ℝ) (N / 2)‖ + 2 :=
    PhaseInterval446.phase_interval_norm_le γ (h : ℝ) N
  have hrescale := hd (η / 6) (by positivity) le_rfl N hNd
  have hscale : calE γ (η / 6) N ^ (-(3 / 2 : ℝ)) =
      Real.exp (-(η / 4) * Real.log N ^ (3 - 2 * γ)) := by
    unfold calE
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [hscale] at hrescale
  exact (hphase.trans (add_le_add hsum (le_refl 2))).trans hrescale

/-- P0082 page364 display23 and page365 Lemma8. Count the outer
upper half arc on the dyadic index interval.
CONDITIONAL ON leaf_interval_majorant524 and U1539.theorem2.
The whole discrepancy statement U1539.lemma4 is not used. -/
theorem dyadic_upper_boundary524 (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((Ioc (N / 2) N).filter (fun n : ℕ =>
          1 - calE γ κ N ^ (-(1 / 8 : ℝ)) / 2 < Int.fract (F γ n))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  classical
  let δ := min ((γ - 1) / 48) (1 / 24)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδsmall : δ < min ((γ - 1) / 24) (1 / 12) := by
    apply lt_min
    · have hd := min_le_left ((γ - 1) / 48) (1 / 24)
      dsimp [δ]
      linarith
    · have hd := min_le_right ((γ - 1) / 48) (1 / 24)
      dsimp [δ]
      linarith
  let C := 6 * δ
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨η, B, hη, hB, Ns, hs⟩ := integer_frequency_decay524 U1539.theorem2 γ δ h1 h2 hδ hδsmall
  obtain ⟨Nr, hr⟩ := cutoff_frequency_range524 γ C h1 hC
  refine ⟨min η 1, lt_min hη (by norm_num), fun κ hκ hκcap =>
    ⟨5 + 8 * B, by positivity, max 16 (max Nr Ns), fun N hN => ?_⟩⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hNr : Nr ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNs : Ns ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hκη : κ ≤ η := hκcap.trans (min_le_left _ _)
  have hκ1 : κ ≤ 1 := hκcap.trans (min_le_right _ _)
  let u := Real.log (N : ℝ) ^ (3 - 2 * γ)
  let Δ := Real.exp (-(κ / 8 * u))
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hu : 0 ≤ u := Real.rpow_nonneg hL.le _
  have hΔ : 0 < Δ := Real.exp_pos _
  have hΔ1 : Δ ≤ 1 := Real.exp_le_one_iff.mpr (by have ht := mul_nonneg (by positivity : 0 ≤ κ / 8) hu; linarith)
  have hfreq := hr N hNr κ hκ.le hκ1
  have hcount := interval_count_of_decay524 (Ioc (N / 2) N) (fun n => F γ n) N
    (1 - Δ / 2) 1 κ η u B hκ.le hκη hu hB.le
    (by simp only [Nat.card_Ioc]; exact_mod_cast Nat.sub_le N (N / 2))
    (by dsimp [Δ]; linarith [Real.exp_pos (-(κ / 8 * u))])
    (by linarith) (leaf_interval_majorant524 _ _ (by linarith) (by linarith) le_rfl _)
    (fun h hh => by
      have hh1 : 1 ≤ h := (Finset.mem_Icc.mp hh).1
      have hhH : (h : ℝ) ≤ (Nat.ceil (Real.exp (κ / 8 * u)) : ℝ) :=
        by exact_mod_cast (Finset.mem_Icc.mp hh).2
      exact hs N hNs h hh1 (hhH.trans hfreq))
  have hsub : ((Ioc (N / 2) N).filter (fun n : ℕ => 1 - Δ / 2 < Int.fract (F γ n))) ⊆
      (Ioc (N / 2) N).filter (fun n : ℕ => 1 - Δ / 2 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < 1) := by
    intro n hn
    obtain ⟨hn, hb⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hn, hb.le, Int.fract_lt_one _⟩
  have hcard : (((Ioc (N / 2) N).filter (fun n : ℕ => 1 - Δ / 2 < Int.fract (F γ n))).card : ℝ) ≤
      (5 + 8 * B) * N * Δ := by
    have hc : (((Ioc (N / 2) N).filter (fun n : ℕ => 1 - Δ / 2 < Int.fract (F γ n))).card : ℝ) ≤
        (((Ioc (N / 2) N).filter (fun n : ℕ => 1 - Δ / 2 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < 1)).card : ℝ) :=
      by exact_mod_cast Finset.card_le_card hsub
    exact hc.trans hcount
  simpa only [boundary_scale524, Δ, u] using hcard


/-- P0082 page364 display23. The lower midpoint piece of the outer
upper arc is contained in the dyadic upper half arc. No discrepancy input
is needed for this finite cardinality comparison. -/
theorem lower_band_card524 (γ κ : ℝ) (N : ℕ) (hγ : 1 < γ) (hN : 16 ≤ N) :
    (((window γ N).filter (fun n : ℕ =>
      n ≤ N ∧ 1 - calE γ κ N ^ (-(1 / 8 : ℝ)) / 2 < Int.fract (F γ n) ∧
        Int.fract (F γ n) ≤ 1 - 1 / 4 * calE γ κ N ^ (-(1 / 8 : ℝ)))).card : ℝ) ≤
      (((Ioc (N / 2) N).filter (fun n : ℕ =>
        1 - calE γ κ N ^ (-(1 / 8 : ℝ)) / 2 < Int.fract (F γ n))).card : ℝ) := by
  classical
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hnW, _, hb, _⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_filter.mpr ⟨Decomp371a.window_subset_Ioc γ hγ N hN hnW, hb⟩


/-- P0082 page364 display23. Positivity of the boundary width puts
the upper midpoint piece inside the outer upper half arc. -/
theorem upper_band_card524 (γ κ : ℝ) (N : ℕ) (hγ : 1 < γ) (hN : 16 ≤ N) :
    (((window γ N).filter (fun n : ℕ =>
      n ≤ N ∧ 1 - 1 / 4 * calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n))).card : ℝ) ≤
      (((Ioc (N / 2) N).filter (fun n : ℕ =>
        1 - calE γ κ N ^ (-(1 / 8 : ℝ)) / 2 < Int.fract (F γ n))).card : ℝ) := by
  classical
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hnW, _, hb⟩ := Finset.mem_filter.mp hn
  have hΔ : 0 < calE γ κ N ^ (-(1 / 8 : ℝ)) := Real.rpow_pos_of_pos (Real.exp_pos _) _
  exact Finset.mem_filter.mpr ⟨Decomp371a.window_subset_Ioc γ hγ N hN hnW, by linarith⟩



end LeanLab.ExceptionalSet.Decomp524a
