import LeanLab.ExceptionalSet.Decomp371a
import LeanLab.ExceptionalSet.SPLIT_lemma4

/-!
P0082 page 354 Theorem 2 and page 359 Lemma 4.
Source: https://doi.org/10.5802/aif.1621
The analytic inputs are finite Erdos Turan and positive integer frequency cancellation.
The unweighted Fourier error below follows by dropping the factors one over h.
No discrepancy estimate or fractional boundary theorem is used as an input.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp523a

open Real Finset Filter Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE eC)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-- LEAF. P0082 page 359 Lemma 4, auxiliary one sided trigonometric
majorant for its omitted finite discrepancy argument. The constant coefficient
pays the interval length plus the reciprocal cutoff. Each other coefficient
has bounded norm. Only an upper bound for the discontinuous indicator is used.
This is a standard analytic majorant input, not asserted as a printed display. -/
theorem leaf_one_sided_majorant :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b : ℝ) (H : ℕ),
      0 ≤ a → a ≤ b → b ≤ 1 → 1 ≤ H →
      ∃ c₀ : ℝ, ∃ c : ℕ → ℂ,
        c₀ ≤ C * (b - a + 1 / ((H : ℝ) + 1)) ∧
        (∀ h ∈ Finset.range H, ‖c h‖ ≤ C) ∧
        ∀ x : ℝ, (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
          c₀ + ∑ h ∈ Finset.range H, (c h * eC (((h : ℝ) + 1) * x)).re := by
  sorry

/-- P0082 page 359 Lemma 4, elementary base case of the one sided
majorant at cutoff one. A constant polynomial suffices at this cutoff.
This base case does not supply the shrinking error needed for the band estimate. -/
theorem one_sided_majorant_at_one (a b : ℝ) (hab : a ≤ b) :
    ∃ c₀ : ℝ, ∃ c : ℕ → ℂ,
      c₀ ≤ 2 * (b - a + 1 / ((1 : ℝ) + 1)) ∧
      (∀ h ∈ Finset.range 1, ‖c h‖ ≤ 2) ∧
      ∀ x : ℝ, (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
        c₀ + ∑ h ∈ Finset.range 1, (c h * eC (((h : ℝ) + 1) * x)).re := by
  refine ⟨1, fun _ => 0, by linarith, ?_, ?_⟩
  · intro h hh
    norm_num
  · intro x
    simp only [zero_mul, Complex.zero_re, Finset.sum_const_zero, add_zero]
    split_ifs <;> norm_num

/-- P0082 page 359 Lemma 4, elementary finite summation of a one sided
trigonometric majorant. This implication has only finite algebra hypotheses. -/
theorem finite_count_of_majorant (s : Finset ℕ) (f : ℕ → ℝ) (a b C c₀ : ℝ)
    (H : ℕ) (c : ℕ → ℂ)
    (hc₀ : c₀ ≤ C * (b - a + 1 / ((H : ℝ) + 1)))
    (hc : ∀ h ∈ Finset.range H, ‖c h‖ ≤ C)
    (hmajor : ∀ x : ℝ, (if a ≤ Int.fract x ∧ Int.fract x < b then (1 : ℝ) else 0) ≤
      c₀ + ∑ h ∈ Finset.range H, (c h * eC (((h : ℝ) + 1) * x)).re) :
    (((s.filter (fun n => a ≤ Int.fract (f n) ∧ Int.fract (f n) < b)).card : ℝ)) ≤
      C * ((b - a) * s.card + (s.card : ℝ) / (H + 1) +
        ∑ h ∈ Finset.range H, ‖∑ n ∈ s, eC (((h : ℝ) + 1) * f n)‖) := by
  classical
  have hcoef (h : ℕ) (hh : h ∈ Finset.range H) :
      (∑ n ∈ s, (c h * eC (((h : ℝ) + 1) * f n)).re) ≤
        C * ‖∑ n ∈ s, eC (((h : ℝ) + 1) * f n)‖ := by
    calc
      _ = (c h * ∑ n ∈ s, eC (((h : ℝ) + 1) * f n)).re := by
        rw [Finset.mul_sum, Complex.re_sum]
      _ ≤ ‖c h * ∑ n ∈ s, eC (((h : ℝ) + 1) * f n)‖ := Complex.re_le_norm _
      _ = ‖c h‖ * ‖∑ n ∈ s, eC (((h : ℝ) + 1) * f n)‖ := norm_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (hc h hh) (norm_nonneg _)
  have hconst : (s.card : ℝ) * c₀ ≤
      C * ((b - a) * s.card + (s.card : ℝ) / (H + 1)) := by
    calc
      _ ≤ (s.card : ℝ) * (C * (b - a + 1 / ((H : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hc₀ (Nat.cast_nonneg _)
      _ = _ := by ring
  calc
    _ = ∑ n ∈ s, if a ≤ Int.fract (f n) ∧ Int.fract (f n) < b then (1 : ℝ) else 0 := by
      simp
    _ ≤ ∑ n ∈ s, (c₀ + ∑ h ∈ Finset.range H, (c h * eC (((h : ℝ) + 1) * f n)).re) :=
      Finset.sum_le_sum (fun n _ => hmajor (f n))
    _ = (s.card : ℝ) * c₀ +
        ∑ h ∈ Finset.range H, ∑ n ∈ s, (c h * eC (((h : ℝ) + 1) * f n)).re := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      simp
    _ ≤ C * ((b - a) * s.card + (s.card : ℝ) / (H + 1)) +
        C * ∑ h ∈ Finset.range H, ‖∑ n ∈ s, eC (((h : ℝ) + 1) * f n)‖ := by
      apply add_le_add hconst
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hcoef
    _ = _ := by ring

/-- LEAF. P0082 page 359 Lemma 4, auxiliary finite Erdos Turan input to the
omitted discrepancy argument. The finite upper count now follows from the
explicit one sided majorant by finite summation. The interval is half open at
its upper end. This remains conditional on leaf_one_sided_majorant. -/
theorem leaf_erdos_turan :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset ℕ) (f : ℕ → ℝ) (a b : ℝ) (H : ℕ),
      0 ≤ a → a ≤ b → b ≤ 1 → 1 ≤ H →
      (((s.filter (fun n => a ≤ Int.fract (f n) ∧ Int.fract (f n) < b)).card : ℝ)) ≤
        C * ((b - a) * s.card + (s.card : ℝ) / (H + 1) +
          ∑ h ∈ Finset.range H, ‖∑ n ∈ s, eC (((h : ℝ) + 1) * f n)‖) := by
  obtain ⟨C, hC, hm⟩ := leaf_one_sided_majorant
  refine ⟨C, hC, fun s f a b H ha hab hb hH => ?_⟩
  obtain ⟨c₀, c, hc₀, hc, hmajor⟩ := hm a b H ha hab hb hH
  exact finite_count_of_majorant s f a b C c₀ H c hc₀ hc hmajor

/-- LEAF. P0082 page 354 Theorem 2, specialized to positive integer frequencies
on the half dyadic interval used on page 359 in Lemma 4. The upper frequency
exponent is half of gamma minus one. The existing open positive frequency input already uses this half dyadic interval.
This elementary specialization uses that input at alpha one. It remains conditional
on U1539.leaf_exp_sum_bound and adds no duplicate analytic admission.
This is an exponential sum input, not a band counting substitute. -/
theorem leaf_integer_frequency (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ η A : ℝ, 0 < η ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ h : ℕ, 1 ≤ h → (h : ℝ) ≤ F γ N ^ ((γ - 1) / 2) →
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC ((h : ℝ) * F γ n)‖ ≤
          A * N * Real.exp (-η * Real.log N ^ (3 - 2 * γ)) := by
  obtain ⟨η, A, hη, hA, hs⟩ := U1539.leaf_exp_sum_bound γ h1 h2
    ((γ - 1) / 2) (by linarith) (by linarith)
  refine ⟨η, A, hη, hA, 2, fun N hN h hh hhF => ?_⟩
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hF : 1 < F γ N := Real.one_lt_exp_iff.mpr (Real.rpow_pos_of_pos hlog _)
  have hfreq : F γ N ^ (-(1 / 2 : ℝ)) < |(1 : ℝ)| := by
    rw [abs_one]
    exact Real.rpow_lt_one_of_one_lt_of_neg hF (by norm_num)
  simpa only [mul_one] using hs N (by omega) 1 hfreq (by norm_num) h hh hhF

/-- P0082 page 365 choice of Delta, auxiliary exponential identity. -/
theorem delta_exp (γ κ : ℝ) (N : ℕ) :
    calE γ κ N ^ (-(1 / 8 : ℝ)) =
      Real.exp (-(κ / 8) * Real.log N ^ (3 - 2 * γ)) := by
  unfold calE
  rw [← Real.exp_mul]
  congr 1
  ring

/-- P0082 page 359 finite truncation, auxiliary choice H equal to the ceiling
of one over Delta. Its reciprocal error is at most Delta. -/
theorem cutoff_bounds (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ ⌈δ⁻¹⌉₊ ∧ δ⁻¹ ≤ (⌈δ⁻¹⌉₊ : ℝ) ∧
      (⌈δ⁻¹⌉₊ : ℝ) ≤ 2 * δ⁻¹ ∧ 1 / ((⌈δ⁻¹⌉₊ : ℝ) + 1) ≤ δ := by
  have hi : 0 < δ⁻¹ := inv_pos.mpr hδ
  have hi1 : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  have hl := Nat.le_ceil δ⁻¹
  have hu := (Nat.ceil_lt_add_one hi.le).le
  refine ⟨Nat.one_le_ceil_iff.mpr hi, hl, by linarith, ?_⟩
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (⌈δ⁻¹⌉₊ : ℝ) + 1)).mpr
  have hm := mul_le_mul_of_nonneg_left hl hδ.le
  rw [mul_inv_cancel₀ hδ.ne'] at hm
  nlinarith

/-- P0082 page 359 discrepancy reduction, elementary finite Fourier error
aggregation. This implication is conditional on its explicit finite count input. -/
theorem count_of_fourier_bound (s : Finset ℕ) (f : ℕ → ℝ) (a b δ A C : ℝ)
    (N H : ℕ) (hδ : 0 < δ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hcard : (s.card : ℝ) ≤ N) (hlen : b - a ≤ δ) (hlen0 : 0 ≤ b - a)
    (hH : (H : ℝ) ≤ 2 * δ⁻¹) (hinv : 1 / ((H : ℝ) + 1) ≤ δ)
    (hfreq : ∀ h ∈ Finset.range H,
      ‖∑ n ∈ s, eC (((h : ℝ) + 1) * f n)‖ ≤ A * N * δ ^ 2)
    (hcount : (((s.filter (fun n => a ≤ Int.fract (f n) ∧ Int.fract (f n) < b)).card : ℝ)) ≤
      C * ((b - a) * s.card + (s.card : ℝ) / (H + 1) +
        ∑ h ∈ Finset.range H, ‖∑ n ∈ s, eC (((h : ℝ) + 1) * f n)‖)) :
    (((s.filter (fun n => a ≤ Int.fract (f n) ∧ Int.fract (f n) < b)).card : ℝ)) ≤
      C * (2 + 2 * A) * N * δ := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hsum : (∑ h ∈ Finset.range H, ‖∑ n ∈ s, eC (((h : ℝ) + 1) * f n)‖) ≤
      (H : ℝ) * (A * N * δ ^ 2) := by
    calc
      _ ≤ ∑ _h ∈ Finset.range H, A * N * δ ^ 2 := Finset.sum_le_sum hfreq
      _ = _ := by simp
  have hfreq' : (H : ℝ) * (A * N * δ ^ 2) ≤ 2 * A * N * δ := by
    calc
      _ ≤ (2 * δ⁻¹) * (A * N * δ ^ 2) :=
        mul_le_mul_of_nonneg_right hH (by positivity)
      _ = _ := by field_simp [hδ.ne']
  have hmain : (b - a) * (s.card : ℝ) ≤ δ * N :=
    (mul_le_mul_of_nonneg_left hcard hlen0).trans
      (mul_le_mul_of_nonneg_right hlen hN)
  have hrem : (s.card : ℝ) / ((H : ℝ) + 1) ≤ N * δ := by
    calc
      _ = (s.card : ℝ) * (1 / ((H : ℝ) + 1)) := by ring
      _ ≤ (s.card : ℝ) * δ := mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _)
      _ ≤ N * δ := mul_le_mul_of_nonneg_right hcard hδ.le
  calc
    _ ≤ C * ((b - a) * s.card + (s.card : ℝ) / (H + 1) +
        ∑ h ∈ Finset.range H, ‖∑ n ∈ s, eC (((h : ℝ) + 1) * f n)‖) := hcount
    _ ≤ C * (δ * N + N * δ + 2 * A * N * δ) := by
      apply mul_le_mul_of_nonneg_left _ hC
      linarith
    _ = _ := by ring

/-- P0082 page 354 Theorem 2, elementary admissibility of the finite Fourier
cutoff. The exponential in log N to power three minus twice gamma grows more
slowly than F to any fixed positive power. -/
theorem cutoff_within_frequency_range (γ κ : ℝ) (h1 : 1 < γ)
    (hκ : 0 < κ) (hκC : κ ≤ 2 * (γ - 1)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (⌈(calE γ κ N ^ (-(1 / 8 : ℝ)))⁻¹⌉₊ : ℝ) ≤
        F γ N ^ ((γ - 1) / 2) := by
  let C : ℝ := (γ - 1) / 2
  have hC : 0 < C := by dsimp [C]; linarith
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun N : ℕ => Real.log N ^ γ) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < γ)).comp hlog
  have he : Tendsto (fun N : ℕ => Real.exp ((C / 2) * Real.log N ^ γ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (hu.const_mul_atTop (by positivity))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((hlog.eventually_ge_atTop 1).and (he.eventually_ge_atTop 2))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hl, he2⟩ := hN₀ N hN
  let t : ℝ := Real.log N ^ (3 - 2 * γ)
  let u : ℝ := Real.log N ^ γ
  have ht : 0 ≤ t := Real.rpow_nonneg (by linarith) _
  have hu0 : 0 ≤ u := Real.rpow_nonneg (by linarith) _
  have htu : t ≤ u := Real.rpow_le_rpow_of_exponent_le hl (by linarith)
  have hx : (κ / 8) * t ≤ (C / 2) * u := by
    have hc : κ / 8 ≤ C / 2 := by dsimp [C]; linarith
    exact (mul_le_mul_of_nonneg_right hc ht).trans
      (mul_le_mul_of_nonneg_left htu (by positivity))
  have hi : (calE γ κ N ^ (-(1 / 8 : ℝ)))⁻¹ = Real.exp ((κ / 8) * t) := by
    rw [delta_exp, ← Real.exp_neg]
    congr 1
    dsimp [t]
    ring
  rw [hi]
  calc
    _ ≤ Real.exp ((κ / 8) * t) + 1 := (Nat.ceil_lt_add_one (Real.exp_pos _).le).le
    _ ≤ 2 * Real.exp ((κ / 8) * t) := by
      have := Real.one_le_exp_iff.mpr (mul_nonneg (by positivity : 0 ≤ κ / 8) ht)
      linarith
    _ ≤ Real.exp ((C / 2) * u) * Real.exp ((C / 2) * u) :=
      mul_le_mul he2 (Real.exp_le_exp.mpr hx) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = F γ N ^ C := by
      rw [← Real.exp_add]
      unfold F
      rw [← Real.exp_mul]
      congr 1
      dsimp [u]
      ring

/-- P0082 page 354 Theorem 2 and page 365 Delta. Shrinking kappa makes the
frequency error no larger than A times N times Delta squared. -/
theorem decay_to_delta_sq (γ κ η A : ℝ) (N : ℕ)
    (hκ : κ ≤ 4 * η) (hA : 0 ≤ A) (hlog : 0 ≤ Real.log N) :
    A * N * Real.exp (-η * Real.log N ^ (3 - 2 * γ)) ≤
      A * N * (calE γ κ N ^ (-(1 / 8 : ℝ))) ^ 2 := by
  have ht : 0 ≤ Real.log N ^ (3 - 2 * γ) := Real.rpow_nonneg hlog _
  rw [delta_exp, ← Real.exp_nat_mul]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hA (Nat.cast_nonneg N))
  apply Real.exp_le_exp.mpr
  norm_num
  nlinarith

/-- P0082 page 365 Delta lies in the interval from zero to one for positive
kappa and nonnegative log N. This is an elementary scale bound. -/
theorem delta_bounds (γ κ : ℝ) (N : ℕ) (hκ : 0 < κ) (hlog : 0 ≤ Real.log N) :
    0 < calE γ κ N ^ (-(1 / 8 : ℝ)) ∧
      calE γ κ N ^ (-(1 / 8 : ℝ)) ≤ 1 := by
  rw [delta_exp]
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr ?_⟩
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.rpow_nonneg hlog _)

/-- P0082 page 359 Lemma 4, upper interval count assembled from the two
explicit analytic leaves. The cap is uniform for all positive smaller kappa.
This result remains conditional on those open leaves. -/
theorem dyadic_band_bound (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, 16 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
        ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
          b - a ≤ calE γ κ N ^ (-(1 / 8 : ℝ)) →
          (((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
            a ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < b)).card : ℝ) ≤
            B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  classical
  obtain ⟨C, hC, hET⟩ := leaf_erdos_turan
  obtain ⟨η, A, hη, hA, Nη, hNη⟩ := leaf_integer_frequency γ h1 h2
  refine ⟨min (2 * (γ - 1)) (4 * η), lt_min (by linarith) (by positivity),
    fun κ hκ hκcap => ?_⟩
  have hκC : κ ≤ 2 * (γ - 1) := hκcap.trans (min_le_left _ _)
  have hκη : κ ≤ 4 * η := hκcap.trans (min_le_right _ _)
  obtain ⟨NF, hNF⟩ := cutoff_within_frequency_range γ κ h1 hκ hκC
  refine ⟨C * (2 + 2 * A), by positivity, max 16 (max Nη NF), le_max_left _ _,
    fun N hN a b ha hab hb hlen => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hNη' : Nη ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNF' : NF ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  let δ : ℝ := calE γ κ N ^ (-(1 / 8 : ℝ))
  let H : ℕ := ⌈δ⁻¹⌉₊
  obtain ⟨hδ, hδ1⟩ := delta_bounds γ κ N hκ hlog
  obtain ⟨hH1, _, hH, hinv⟩ := cutoff_bounds δ hδ hδ1
  have hfreq (h : ℕ) (hh : h ∈ Finset.range H) :
      ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (((h : ℝ) + 1) * F γ n)‖ ≤ A * N * δ ^ 2 := by
    have hhH : h + 1 ≤ H := by have := Finset.mem_range.mp hh; omega
    have hhF : ((h + 1 : ℕ) : ℝ) ≤ F γ N ^ ((γ - 1) / 2) :=
      (by exact_mod_cast hhH : ((h + 1 : ℕ) : ℝ) ≤ (H : ℝ)).trans (hNF N hNF')
    have he := hNη N hNη' (h + 1) (by omega) hhF
    simp only [Nat.cast_add, Nat.cast_one] at he
    exact he.trans (decay_to_delta_sq γ κ η A N hκη hA.le hlog)
  have hcard : ((Finset.Ioc (N / 2) N).card : ℝ) ≤ N := by
    rw [Nat.card_Ioc]
    exact_mod_cast (Nat.sub_le N (N / 2))
  exact count_of_fourier_bound (Finset.Ioc (N / 2) N) (fun n => F γ n)
    a b δ A C N H hδ hA.le hC.le hcard hlen (sub_nonneg.mpr hab) hH hinv hfreq
    (hET _ _ a b H ha hab hb hH1)

/-- P0082 page 365 floor window, elementary subset transfer of a half open
band count on the dyadic index interval. No distribution input is hidden here. -/
theorem window_band_transfer (γ a b B δ : ℝ) (N : ℕ) (h1 : 1 < γ) (hN : 16 ≤ N)
    (hcount : (((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
      a ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < b)).card : ℝ) ≤ B * N * δ) :
    (((window γ N).filter (fun n : ℕ =>
      n ≤ N ∧ a ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < b)).card : ℝ) ≤ B * N * δ := by
  classical
  refine le_trans ?_ hcount
  exact_mod_cast Finset.card_le_card (show
    (window γ N).filter (fun n : ℕ => n ≤ N ∧ a ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < b) ⊆
      (Finset.Ioc (N / 2) N).filter (fun n : ℕ => a ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < b) from by
        intro n hn
        obtain ⟨hnW, _, hband⟩ := Finset.mem_filter.mp hn
        exact Finset.mem_filter.mpr ⟨Decomp371a.window_subset_Ioc γ h1 N hN hnW, hband⟩)

end LeanLab.ExceptionalSet.Decomp523a
