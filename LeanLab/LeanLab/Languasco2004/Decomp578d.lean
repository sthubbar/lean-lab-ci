/-
Jia 1996 pages 261, 262 and 283 to 285.
Source https://doi.org/10.4064/aa-77-3-207-287.
The Buchstab inputs, integer sieve comparison and prime summation are separate.
Analytic leaves stay OPEN. The exact supplied assemblies are CONDITIONAL.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp578c

namespace LeanLab.Languasco2004.Decomp578d
open Real Finset intervalIntegral Decomp279a Decomp316a Source565 Sieve565 Numeric565 Reserve578
noncomputable section
attribute [local instance] Classical.propDecidable
open Decomp578c

/-- Pages 284 and 285: the weighted reciprocal triple prime sum.
Below the middle boundary Lemma 20 gives 0.5617. Above it the bound is 0.5644.
The relaxed third prime interval has the exact source half open endpoints. -/
def triplePrimeModel (Y : ℝ) (n : ℕ) : ℝ :=
  (135 / 16) * ∑ pq ∈ pairDomain true Y n,
    ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
      Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
      (if (pq.1 : ℝ) * (pq.2 : ℝ) ^ (2 : ℕ) ≤ Y ^ (71 / 135 : ℝ)
        then 0.5617 else 0.5644) / ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ))

/-- Jia pages 284 and 285: the argument bookkeeping of the printed constant cut.
For a source triple `p q r` the Buchstab argument `log (Y / (p q r)) / log α` is strictly
above `3`, so Lemma 20 part ii gives the `0.5644` bound used in the model. -/
private lemma triple_argument_gt_three {Y p q r : ℝ} (hY : 1 < Y) (hp : 0 < p) (hq : 0 < q)
    (hr : 0 < r) (hqp : q < p) (hpB : p ≤ Y ^ (89 / 462 - 0.00000001 : ℝ)) (hrq : r < q) :
    3 < Real.log (Y / (p * q * r)) / Real.log (Y ^ (16 / 135 : ℝ)) := by
  have hY0 : 0 < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hpB' : Real.log p ≤ (89 / 462 - 0.00000001) * Real.log Y := by
    calc Real.log p ≤ Real.log (Y ^ (89 / 462 - 0.00000001 : ℝ)) := Real.log_le_log hp hpB
      _ = (89 / 462 - 0.00000001) * Real.log Y := Real.log_rpow hY0 _
  have hqlt : Real.log q < Real.log p := Real.log_lt_log hq hqp
  have hlogq : Real.log q < (89 / 462) * Real.log Y := by nlinarith [hpB', hqlt]
  have hlogr : Real.log r < (89 / 462) * Real.log Y :=
    lt_trans (Real.log_lt_log hr hrq) hlogq
  have hlogpqr : Real.log (p * q * r) = Real.log p + (Real.log q + Real.log r) := by
    rw [Real.log_mul (mul_ne_zero hp.ne' hq.ne') hr.ne', Real.log_mul hp.ne' hq.ne']
    ring
  have hupper : Real.log (p * q * r) < (267 / 462) * Real.log Y := by
    rw [hlogpqr]
    nlinarith [hpB', hlogq, hlogr]
  have hsplit : Real.log (Y / (p * q * r)) = Real.log Y - Real.log (p * q * r) :=
    Real.log_div hY0.ne' (by positivity)
  have hlogα : Real.log (Y ^ (16 / 135 : ℝ)) = (16 / 135) * Real.log Y := Real.log_rpow hY0 _
  rw [hsplit, hlogα, lt_div_iff₀ (by nlinarith)]
  nlinarith

/-- Jia page 284: below the middle boundary the argument is at least `4`, so Lemma 20
part iii gives the sharper `0.5617` bound used in the model. -/
private lemma triple_argument_ge_four {Y p q r : ℝ} (hY : 1 < Y) (hp : 0 < p) (hq : 0 < q)
    (hr : 0 < r) (hrq : r < q) (hsmall : p * q ^ 2 ≤ Y ^ (71 / 135 : ℝ)) :
    4 ≤ Real.log (Y / (p * q * r)) / Real.log (Y ^ (16 / 135 : ℝ)) := by
  have hY0 : 0 < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hgrowth : p * q * r < p * q ^ 2 := by
    calc p * q * r < p * q * q := by
          exact mul_lt_mul_of_pos_left hrq (by positivity)
      _ = p * q ^ 2 := by ring
  have hlt : Real.log (p * q * r) < Real.log (p * q ^ 2) :=
    Real.log_lt_log (by positivity) hgrowth
  have hsmall' : Real.log (p * q ^ 2) ≤ (71 / 135) * Real.log Y := by
    calc Real.log (p * q ^ 2) ≤ Real.log (Y ^ (71 / 135 : ℝ)) :=
          Real.log_le_log (by positivity) hsmall
      _ = (71 / 135) * Real.log Y := Real.log_rpow hY0 _
  have hlogpqr : Real.log (p * q * r) < (71 / 135) * Real.log Y := lt_of_lt_of_le hlt hsmall'
  have hsplit : Real.log (Y / (p * q * r)) = Real.log Y - Real.log (p * q * r) :=
    Real.log_div hY0.ne' (by positivity)
  have hlogα : Real.log (Y ^ (16 / 135 : ℝ)) = (16 / 135) * Real.log Y := Real.log_rpow hY0 _
  rw [hsplit, hlogα, le_div_iff₀ (by nlinarith)]
  nlinarith

/-- Jia page 285: the exponent change of variable `α = Y^(16/135)` turns the model
denominator `log α` into the source `(135/16) * Y / log Y`, exactly. -/
private lemma log_rpow_sixteen {Y : ℝ} (hY : 1 < Y) :
    Y / Real.log (Y ^ (16 / 135 : ℝ)) = (135 / 16) * (Y / Real.log Y) := by
  have hY0 : 0 < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  rw [Real.log_rpow hY0]
  field_simp
  try ring

/-- Jia page 262 Lemma 20 part ii as used on the upper branch of the triple sum. -/
private lemma triple_weight_le_high (h20 : type_of% lemma20_global_bounds) (w : ℝ → ℝ)
    (hw : ContinuousOn w (Set.Ici 1))
    (hi : ∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u)
    (hr : ∀ u : ℝ, 2 ≤ u → u * w u = 1 + ∫ t in (1 : ℝ)..(u - 1), w t)
    {u : ℝ} (hu : 3 ≤ u) : w u ≤ 0.5644 :=
  (h20 w hw hi hr).1 u hu

/-- Jia page 262 Lemma 20 part iii as used on the lower branch of the triple sum. -/
private lemma triple_weight_le_sharp (h20 : type_of% lemma20_global_bounds) (w : ℝ → ℝ)
    (hw : ContinuousOn w (Set.Ici 1))
    (hi : ∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u)
    (hr : ∀ u : ℝ, 2 ≤ u → u * w u = 1 + ∫ t in (1 : ℝ)..(u - 1), w t)
    {u : ℝ} (hu : 4 ≤ u) : w u ≤ 0.5617 :=
  (h20 w hw hi hr).2 u hu |>.2


-- === prime windows (Chebyshev) ===
/-- Chebyshev's bound on a dyadic window of primes. -/
lemma card_primes_dyadic_le (A : ℝ) (hA : 0 < A) :
    (((Icc ⌈A⌉₊ ⌊2 * A⌋₊).filter (fun p : ℕ => p.Prime)).card : ℝ) * Real.log A
      ≤ Real.log 4 * (2 * A) := by
  have h2A : (0 : ℝ) ≤ 2 * A := by linarith
  set s : Finset ℕ := (Icc ⌈A⌉₊ ⌊2 * A⌋₊).filter (fun p : ℕ => p.Prime) with hs
  have hge : ∀ p ∈ s, A ≤ (p : ℝ) := by
    intro p hp
    have h1 : ⌈A⌉₊ ≤ p := (mem_Icc.mp (mem_filter.mp hp).1).1
    have h2 : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
    have h3 : (⌈A⌉₊ : ℝ) ≤ (p : ℝ) := by exact_mod_cast h1
    linarith
  have hstep : (s.card : ℝ) * Real.log A = ∑ p ∈ s, Real.log A := by
    rw [sum_const, nsmul_eq_mul]
  rw [hstep]
  have hle : ∑ p ∈ s, Real.log A ≤ ∑ p ∈ s, Real.log p := by
    refine sum_le_sum fun p hp => ?_
    exact Real.log_le_log hA (hge p hp)
  have hsub : s ⊆ Nat.primesLE ⌊2 * A⌋₊ := by
    intro p hp
    have hf := mem_filter.mp hp
    have hle2 : p ≤ ⌊2 * A⌋₊ := (mem_Icc.mp hf.1).2
    rw [Nat.primesLE_eq_filter_range]
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hle2), hf.2⟩
  have htheta : ∑ p ∈ s, Real.log p ≤ Chebyshev.theta (2 * A) := by
    rw [Chebyshev.theta_eq_sum_primesLE]
    refine sum_le_sum_of_subset_of_nonneg hsub ?_
    intro p hp _
    rw [Nat.primesLE_eq_filter_range] at hp
    have hpp : p.Prime := (mem_filter.mp hp).2
    exact Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
  exact hle.trans (htheta.trans (Chebyshev.theta_le_log4_mul_x h2A))

/-- Reciprocal sum over one dyadic window of primes. -/
lemma sum_inv_primes_dyadic_le (A : ℝ) (hA : 1 < A) :
    ∑ p ∈ (Icc ⌈A⌉₊ ⌊2 * A⌋₊).filter (fun p : ℕ => p.Prime), (1 : ℝ) / (p : ℝ)
      ≤ 2 * Real.log 4 / Real.log A := by
  have hA0 : (0 : ℝ) < A := by linarith
  have hlogA : 0 < Real.log A := Real.log_pos hA
  set s : Finset ℕ := (Icc ⌈A⌉₊ ⌊2 * A⌋₊).filter (fun p : ℕ => p.Prime) with hs
  have hge : ∀ p ∈ s, A ≤ (p : ℝ) := by
    intro p hp
    have h1 : ⌈A⌉₊ ≤ p := (mem_Icc.mp (mem_filter.mp hp).1).1
    have h2 : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
    have h3 : (⌈A⌉₊ : ℝ) ≤ (p : ℝ) := by exact_mod_cast h1
    linarith
  have hsum : ∑ p ∈ s, (1 : ℝ) / (p : ℝ) ≤ (s.card : ℝ) * (1 / A) := by
    have h1 : ∑ p ∈ s, (1 : ℝ) / (p : ℝ) ≤ ∑ _p ∈ s, (1 / A : ℝ) := by
      refine sum_le_sum fun p hp => ?_
      exact one_div_le_one_div_of_le hA0 (hge p hp)
    simpa [sum_const, nsmul_eq_mul] using h1
  have hcard := card_primes_dyadic_le A hA0
  have hbound : (s.card : ℝ) ≤ Real.log 4 * (2 * A) / Real.log A := by
    rw [le_div_iff₀ hlogA]
    linarith
  calc ∑ p ∈ s, (1 : ℝ) / (p : ℝ) ≤ (s.card : ℝ) * (1 / A) := hsum
    _ ≤ (Real.log 4 * (2 * A) / Real.log A) * (1 / A) :=
        mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = 2 * Real.log 4 / Real.log A := by
        field_simp
        try ring

/-- The reciprocal sum of the primes in a window with `log Z ≤ 2 log X` is bounded. -/
lemma sum_inv_primes_window_le {X Z : ℝ} (hX : 1 < X) (hXZ : X ≤ Z)
    (hlogX1 : 1 ≤ Real.log X) (hratio : Real.log Z ≤ 2 * Real.log X) :
    ∑ p ∈ (Icc ⌈X⌉₊ ⌊Z⌋₊).filter (fun p : ℕ => p.Prime), (1 : ℝ) / (p : ℝ)
      ≤ 2 * Real.log 4 * (1 / Real.log 2 + 1) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set s : Finset ℕ := (Icc ⌈X⌉₊ ⌊Z⌋₊).filter (fun p : ℕ => p.Prime) with hs
  set kk : ℕ → ℕ := fun p => ⌊Real.log ((p : ℝ) / X) / Real.log 2⌋₊ with hkk
  have hple : ∀ p ∈ s, (p : ℝ) ≤ Z := by
    intro p hp
    have h1 : p ≤ ⌊Z⌋₊ := (mem_Icc.mp (mem_filter.mp hp).1).2
    have h2 : (⌊Z⌋₊ : ℝ) ≤ Z := Nat.floor_le (by linarith)
    calc (p : ℝ) ≤ (⌊Z⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ Z := h2
  have himg : (s.image kk).card ≤ ⌊Real.log (Z / X) / Real.log 2⌋₊ + 1 := by
    have hsub : s.image kk ⊆ Finset.range (⌊Real.log (Z / X) / Real.log 2⌋₊ + 1) := by
      intro y hy
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hy
      have hpX : X ≤ (p : ℝ) := by
        have h1 : ⌈X⌉₊ ≤ p := (mem_Icc.mp (mem_filter.mp hp).1).1
        exact le_trans (Nat.le_ceil X) (by exact_mod_cast h1)
      have hpos : (0 : ℝ) < (p : ℝ) := by linarith
      have hle : (p : ℝ) / X ≤ Z / X :=
        div_le_div_of_nonneg_right (hple p hp) hX0.le
      have hlogle : Real.log ((p : ℝ) / X) / Real.log 2 ≤ Real.log (Z / X) / Real.log 2 :=
        div_le_div_of_nonneg_right (Real.log_le_log (by positivity) hle) hlog2.le
      rw [mem_range]
      exact Nat.lt_succ_of_le (Nat.floor_mono hlogle)
    exact le_trans (card_le_card hsub) (by simp)
  have hfib : ∀ y ∈ s.image kk,
      ∑ p ∈ s.filter (fun p => kk p = y), (1 : ℝ) / (p : ℝ) ≤ 2 * Real.log 4 / Real.log X := by
    intro y hy
    set A : ℝ := X * 2 ^ y with hAdef
    have hA1 : 1 < A := by
      have h1 : (1 : ℝ) ≤ 2 ^ y := one_le_pow₀ (by norm_num)
      rw [hAdef]
      nlinarith
    have hlogA : Real.log A = Real.log X + (y : ℝ) * Real.log 2 := by
      rw [hAdef, Real.log_mul hX0.ne' (by positivity), Real.log_pow]
      try norm_num
    have hsub2 : s.filter (fun p => kk p = y) ⊆
        (Icc ⌈A⌉₊ ⌊2 * A⌋₊).filter (fun p : ℕ => p.Prime) := by
      intro p hp
      have h1 := mem_filter.mp hp
      have h2 := mem_filter.mp h1.1
      have hpr : p.Prime := h2.2
      have hpX : X ≤ (p : ℝ) := by
        have h3 : ⌈X⌉₊ ≤ p := (mem_Icc.mp h2.1).1
        exact le_trans (Nat.le_ceil X) (by exact_mod_cast h3)
      have hpos : (0 : ℝ) < (p : ℝ) := by
        have := hpr.pos
        exact_mod_cast this
      have hlognn : (0 : ℝ) ≤ Real.log ((p : ℝ) / X) :=
        Real.log_nonneg (by rw [le_div_iff₀ hX0]; linarith)
      have hquot : (0 : ℝ) ≤ Real.log ((p : ℝ) / X) / Real.log 2 := div_nonneg hlognn hlog2.le
      have hy1 : ((⌊Real.log ((p : ℝ) / X) / Real.log 2⌋₊ : ℕ) : ℝ)
          ≤ Real.log ((p : ℝ) / X) / Real.log 2 := Nat.floor_le hquot
      have hy2 : Real.log ((p : ℝ) / X) / Real.log 2
          < ((⌊Real.log ((p : ℝ) / X) / Real.log 2⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      have hkey' : ⌊Real.log ((p : ℝ) / X) / Real.log 2⌋₊ = y := h1.2
      rw [hkey'] at hy1 hy2
      push_cast at hy1 hy2
      have hlow : (y : ℝ) * Real.log 2 ≤ Real.log ((p : ℝ) / X) := by
        rw [le_div_iff₀ hlog2] at hy1
        exact hy1
      have hhigh : Real.log ((p : ℝ) / X) < ((y : ℝ) + 1) * Real.log 2 := by
        rw [div_lt_iff₀ hlog2] at hy2
        exact hy2
      have hexp : Real.exp ((y : ℝ) * Real.log 2) = (2 : ℝ) ^ y := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      have hexp2 : Real.exp (((y : ℝ) + 1) * Real.log 2) = (2 : ℝ) ^ (y + 1) := by
        rw [show ((y : ℝ) + 1) * Real.log 2 = (y : ℝ) * Real.log 2 + Real.log 2 by ring,
          Real.exp_add, hexp, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        rw [pow_succ]
        try ring
      have hgeA : A ≤ (p : ℝ) := by
        have h2' : Real.exp ((y : ℝ) * Real.log 2) ≤ (p : ℝ) / X := by
          have := Real.exp_le_exp.mpr hlow
          rwa [Real.exp_log (by positivity)] at this
        rw [le_div_iff₀ hX0] at h2'
        rw [hAdef, mul_comm X, ← hexp]
        exact h2'
      have hle2A : (p : ℝ) ≤ 2 * A := by
        have h2' : (p : ℝ) / X < Real.exp (((y : ℝ) + 1) * Real.log 2) := by
          have := Real.exp_lt_exp.mpr hhigh
          rwa [Real.exp_log (by positivity)] at this
        rw [div_lt_iff₀ hX0] at h2'
        rw [hexp2] at h2'
        have hpow : (2 : ℝ) ^ (y + 1) = 2 * 2 ^ y := by
          rw [pow_succ]
          ring
        rw [hpow] at h2'
        rw [hAdef]
        calc (p : ℝ) ≤ 2 * 2 ^ y * X := le_of_lt h2'
          _ = 2 * (X * 2 ^ y) := by ring
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.ceil_le.mpr hgeA, Nat.le_floor hle2A⟩, hpr⟩
    calc ∑ p ∈ s.filter (fun p => kk p = y), (1 : ℝ) / (p : ℝ)
        ≤ ∑ p ∈ (Icc ⌈A⌉₊ ⌊2 * A⌋₊).filter (fun p : ℕ => p.Prime), (1 : ℝ) / (p : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun x _ _ => by positivity)
      _ ≤ 2 * Real.log 4 / Real.log A := sum_inv_primes_dyadic_le A hA1
      _ ≤ 2 * Real.log 4 / Real.log X := by
          have hlogAle : Real.log X ≤ Real.log A := by
            rw [hlogA]
            have : (0 : ℝ) ≤ (y : ℝ) * Real.log 2 := by positivity
            linarith
          exact div_le_div_of_nonneg_left (by positivity) hlogX hlogAle
  have hKle : ((⌊Real.log (Z / X) / Real.log 2⌋₊ + 1 : ℕ) : ℝ) ≤ Real.log X / Real.log 2 + 1 := by
    have hZ0 : Z ≠ 0 := by linarith
    have hZ : Real.log (Z / X) = Real.log Z - Real.log X := Real.log_div hZ0 hX0.ne'
    have h2' : Real.log (Z / X) ≤ Real.log X := by
      rw [hZ]
      linarith
    have hnn : (0 : ℝ) ≤ Real.log (Z / X) / Real.log 2 := by
      apply div_nonneg _ hlog2.le
      have h0 : (0 : ℝ) ≤ Real.log (Z / X) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ hX0]
        linarith
      exact h0
    have h3 : ((⌊Real.log (Z / X) / Real.log 2⌋₊ : ℕ) : ℝ) ≤ Real.log X / Real.log 2 := by
      calc ((⌊Real.log (Z / X) / Real.log 2⌋₊ : ℕ) : ℝ)
          ≤ Real.log (Z / X) / Real.log 2 := Nat.floor_le hnn
        _ ≤ Real.log X / Real.log 2 := div_le_div_of_nonneg_right h2' hlog2.le
    push_cast
    linarith
  calc ∑ p ∈ s, (1 : ℝ) / (p : ℝ)
      = ∑ y ∈ s.image kk, ∑ p ∈ s.filter (fun p => kk p = y), (1 : ℝ) / (p : ℝ) := by
        rw [sum_fiberwise_of_maps_to]
        intro p hp
        exact mem_image_of_mem kk hp
    _ ≤ ∑ y ∈ s.image kk, 2 * Real.log 4 / Real.log X := sum_le_sum hfib
    _ = ((s.image kk).card : ℝ) * (2 * Real.log 4 / Real.log X) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ((⌊Real.log (Z / X) / Real.log 2⌋₊ + 1 : ℕ) : ℝ) * (2 * Real.log 4 / Real.log X) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast himg
    _ ≤ (Real.log X / Real.log 2 + 1) * (2 * Real.log 4 / Real.log X) :=
        mul_le_mul_of_nonneg_right hKle (by positivity)
    _ = 2 * Real.log 4 * (1 / Real.log 2 + 1 / Real.log X) := by
        field_simp
        try ring
    _ ≤ 2 * Real.log 4 * (1 / Real.log 2 + 1) := by
        have hinv : 1 / Real.log X ≤ 1 := by
          rw [div_le_one hlogX]
          exact hlogX1
        have h4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
        nlinarith


-- === the d-rescaling identity ===
/-- Rescaling by `d = p*q*r`: the count of source integers divisible by `d` and free of prime
factors below `α` equals the sieved count of the rescaled interval at `t = Y/d`. -/
lemma triple_rescale_card_le (Y : ℝ) (n : ℕ) {p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hrq : r < q) (hqp : q < p) (hY : 0 < Y) :
    (sieved ((sourceSet true 0 Y n (p * q)).filter (fun a => r ∣ a)) 1 (Y ^ (16 / 135 : ℝ))).card
      ≤ (sieved (Ioc ⌊Y / ((p * q * r : ℕ) : ℝ)⌋₊
          ⌊2 * (Y / ((p * q * r : ℕ) : ℝ))⌋₊) 1 (Y ^ (16 / 135 : ℝ))).card := by
  set d : ℕ := p * q * r with hd
  set z : ℝ := Y ^ (16 / 135 : ℝ) with hz
  set s : Finset ℕ := sieved ((sourceSet true 0 Y n (p * q)).filter (fun a => r ∣ a)) 1 z with hs
  set t : Finset ℕ := sieved (Ioc ⌊Y / (d : ℝ)⌋₊ ⌊2 * (Y / (d : ℝ))⌋₊) 1 z with ht
  have hdpos : 0 < d := by
    rw [hd]
    exact Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  have hcop : Nat.Coprime (p * q) r := by
    rw [Nat.coprime_mul_iff_left]
    exact ⟨(Nat.coprime_primes hp hr).mpr (by omega), (Nat.coprime_primes hq hr).mpr (by omega)⟩
  have hdata : ∀ a ∈ s, (p * q) ∣ a ∧ r ∣ a ∧ Y < (a : ℝ) ∧ (a : ℝ) ≤ 2 * Y ∧
      (∀ p' : ℕ, p'.Prime → (p' : ℝ) < z → ¬ p' ∣ 1 → ¬ p' ∣ a) := by
    intro a ha
    rw [hs] at ha
    have h1 := mem_filter.mp ha
    have h2 := mem_filter.mp h1.1
    have h3 := mem_filter.mp h2.1
    have hwin : Y < (a : ℝ) ∧ (a : ℝ) ≤ 2 * Y := by simpa using h3.2.2
    exact ⟨h3.2.1, h2.2, hwin.1, hwin.2, h1.2⟩
  have hdvdD : ∀ a ∈ s, d ∣ a := by
    intro a ha
    obtain ⟨h1, h2, -, -, -⟩ := hdata a ha
    have := hcop.mul_dvd_of_dvd_of_dvd h1 h2
    simpa [hd] using this
  have hsub : s.image (fun a => a / d) ⊆ t := by
    intro m hm
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hm
    obtain ⟨-, -, hlow, hhigh, hsieve⟩ := hdata a ha
    have hda := hdvdD a ha
    have hkey : (a / d) * d = a := Nat.div_mul_cancel hda
    have hkeyR : ((a / d : ℕ) : ℝ) * (d : ℝ) = (a : ℝ) := by exact_mod_cast hkey
    have hlowR : Y / (d : ℝ) < ((a / d : ℕ) : ℝ) := by
      rw [div_lt_iff₀ hdR, hkeyR]
      exact hlow
    have hfloor : ⌊Y / (d : ℝ)⌋₊ < a / d := by
      have h1 : ((⌊Y / (d : ℝ)⌋₊ : ℕ) : ℝ) ≤ Y / (d : ℝ) := Nat.floor_le (by positivity)
      have h2 : ((⌊Y / (d : ℝ)⌋₊ : ℕ) : ℝ) < ((a / d : ℕ) : ℝ) := lt_of_le_of_lt h1 hlowR
      exact_mod_cast h2
    have hhiR : ((a / d : ℕ) : ℝ) ≤ 2 * (Y / (d : ℝ)) := by
      have h2 : ((a / d : ℕ) : ℝ) * (d : ℝ) ≤ 2 * Y := by
        rw [hkeyR]
        exact hhigh
      have h3 : ((a / d : ℕ) : ℝ) ≤ 2 * Y / (d : ℝ) := (le_div_iff₀ hdR).mpr h2
      calc ((a / d : ℕ) : ℝ) ≤ 2 * Y / (d : ℝ) := h3
        _ = 2 * (Y / (d : ℝ)) := by ring
    have hlefloor : a / d ≤ ⌊2 * (Y / (d : ℝ))⌋₊ := Nat.le_floor hhiR
    rw [ht]
    refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨hfloor, hlefloor⟩, ?_⟩
    intro p' hp' hlt hnot1 hpd
    exact hsieve p' hp' hlt hnot1 (hkey ▸ dvd_mul_of_dvd_left hpd d)
  have hinj : Set.InjOn (fun a => a / d) ↑s := by
    intro a ha b hb hab
    have hda := hdvdD a ha
    have hdb := hdvdD b hb
    calc a = (a / d) * d := (Nat.div_mul_cancel hda).symm
      _ = (b / d) * d := by rw [show a / d = b / d from hab]
      _ = b := Nat.div_mul_cancel hdb
  have hcard : s.card ≤ t.card := by
    calc s.card = (s.image (fun a => a / d)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ t.card := Finset.card_le_card hsub
  simpa only [← hs, ← ht, ← hz] using hcard


-- === the per-term Lemma 21 bound and the model unfolding ===
/-- Jia page 284 after display 63: the per-term bound on one source triple. Lemma 21 at
`t = Y/(p q r)`, `z = α`, together with the rescaling and Lemma 20's constant branch. -/
lemma triple_term_le {Y : ℝ} {n p q r : ℕ} {w : ℝ → ℝ} {T0 Z0 η₁ : ℝ}
    (h20 : type_of% lemma20_global_bounds) (hw : ContinuousOn w (Set.Ici 1))
    (hi : ∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u)
    (hrec : ∀ u : ℝ, 2 ≤ u → u * w u = 1 + ∫ t in (1 : ℝ)..(u - 1), w t)
    (h21 : ∀ t z : ℝ, T0 ≤ t → Z0 ≤ z → z ≤ t →
      |((sieved (Ioc ⌊t⌋₊ ⌊2 * t⌋₊) 1 z).card : ℝ) -
          w (Real.log t / Real.log z) * (t / Real.log z)| ≤ η₁ * (t / Real.log z))
    (hη : 0 < η₁)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hrq : r < q) (hqp : q < p) (hY : 1 < Y)
    (hpα : Y ^ (16 / 135 : ℝ) < (p : ℝ))
    (hpβ : (p : ℝ) ≤ Y ^ (89 / 462 - 0.00000001 : ℝ))
    (hT : T0 ≤ Y / ((p * q * r : ℕ) : ℝ))
    (hZ : Z0 ≤ Y ^ (16 / 135 : ℝ))
    (hzt : Y ^ (16 / 135 : ℝ) ≤ Y / ((p * q * r : ℕ) : ℝ)) :
    ((sieved ((sourceSet true 0 Y n (p * q)).filter (fun a => r ∣ a)) 1
        (Y ^ (16 / 135 : ℝ))).card : ℝ)
      ≤ (if (p : ℝ) * (q : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then (0.5617 : ℝ) else 0.5644) *
          (Y / ((p * q * r : ℕ) : ℝ) / Real.log (Y ^ (16 / 135 : ℝ)))
        + η₁ * (Y / ((p * q * r : ℕ) : ℝ) / Real.log (Y ^ (16 / 135 : ℝ))) := by
  have hY0 : 0 < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hαpos : (0 : ℝ) < Y ^ (16 / 135 : ℝ) := Real.rpow_pos_of_pos hY0 _
  have hz0 : (0 : ℝ) < Real.log (Y ^ (16 / 135 : ℝ)) := by
    rw [Real.log_rpow hY0]
    positivity
  have hTnn : (0 : ℝ) ≤ Y / ((p * q * r : ℕ) : ℝ) / Real.log (Y ^ (16 / 135 : ℝ)) := by
    apply div_nonneg
    · positivity
    · exact hz0.le
  have hres := triple_rescale_card_le Y n hp hq hr hrq hqp hY0
  have h21' := h21 (Y / ((p * q * r : ℕ) : ℝ)) (Y ^ (16 / 135 : ℝ)) hT hZ hzt
  have hkey : ((sieved (Ioc ⌊Y / ((p * q * r : ℕ) : ℝ)⌋₊
        ⌊2 * (Y / ((p * q * r : ℕ) : ℝ))⌋₊) 1 (Y ^ (16 / 135 : ℝ))).card : ℝ)
      ≤ w (Real.log (Y / ((p * q * r : ℕ) : ℝ)) / Real.log (Y ^ (16 / 135 : ℝ))) *
          (Y / ((p * q * r : ℕ) : ℝ) / Real.log (Y ^ (16 / 135 : ℝ)))
        + η₁ * (Y / ((p * q * r : ℕ) : ℝ) / Real.log (Y ^ (16 / 135 : ℝ))) := by
    have h := (abs_le.mp h21').2
    linarith
  have hcast : ((p * q * r : ℕ) : ℝ) = (p : ℝ) * (q : ℝ) * (r : ℝ) := by push_cast; ring
  have hpq' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hqq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  have hrq' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr.pos
  have hqrlt : (r : ℝ) < (q : ℝ) := by exact_mod_cast hrq
  have hqplt : (q : ℝ) < (p : ℝ) := by exact_mod_cast hqp
  have hc : w (Real.log (Y / ((p * q * r : ℕ) : ℝ)) / Real.log (Y ^ (16 / 135 : ℝ))) ≤
      (if (p : ℝ) * (q : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then (0.5617 : ℝ) else 0.5644) := by
    split_ifs with hsmall
    · rw [hcast]
      exact triple_weight_le_sharp h20 w hw hi hrec
        (triple_argument_ge_four hY hpq' hqq' hrq' hqrlt hsmall)
    · rw [hcast]
      exact triple_weight_le_high h20 w hw hi hrec
        (le_of_lt (triple_argument_gt_three hY hpq' hqq' hrq' hqplt hpβ hqrlt))
  calc ((sieved ((sourceSet true 0 Y n (p * q)).filter (fun a => r ∣ a)) 1
        (Y ^ (16 / 135 : ℝ))).card : ℝ)
      ≤ ((sieved (Ioc ⌊Y / ((p * q * r : ℕ) : ℝ)⌋₊
          ⌊2 * (Y / ((p * q * r : ℕ) : ℝ))⌋₊) 1 (Y ^ (16 / 135 : ℝ))).card : ℝ) := by
        exact_mod_cast hres
    _ ≤ w (Real.log (Y / ((p * q * r : ℕ) : ℝ)) / Real.log (Y ^ (16 / 135 : ℝ))) *
          (Y / ((p * q * r : ℕ) : ℝ) / Real.log (Y ^ (16 / 135 : ℝ)))
        + η₁ * (Y / ((p * q * r : ℕ) : ℝ) / Real.log (Y ^ (16 / 135 : ℝ))) := hkey
    _ ≤ (if (p : ℝ) * (q : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then (0.5617 : ℝ) else 0.5644) *
          (Y / ((p * q * r : ℕ) : ℝ) / Real.log (Y ^ (16 / 135 : ℝ)))
        + η₁ * (Y / ((p * q * r : ℕ) : ℝ) / Real.log (Y ^ (16 / 135 : ℝ))) := by
        have := mul_le_mul_of_nonneg_right hc hTnn
        linarith

/-- `tripleMass` as the double sum of rescaled sieved counts, with the vacuous
`¬ r ∣ 1` condition removed. -/
lemma tripleMass_eq_double_sum (Y : ℝ) (n : ℕ) :
    tripleMass true true 0 Y n (Y ^ (16 / 135 : ℝ)) (Y ^ (16 / 135 : ℝ))
      = ∑ pq ∈ pairDomain true Y n,
          ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
            Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
          ((sieved ((sourceSet true 0 Y n (pq.1 * pq.2)).filter (fun a => r ∣ a)) 1
            (Y ^ (16 / 135 : ℝ))).card : ℝ) := by
  simp only [tripleMass, tripleSieved, if_true]
  refine Finset.sum_congr rfl (fun pq _ => ?_)
  refine Finset.sum_congr ?_ (fun r _ => rfl)
  ext r
  simp only [mem_filter]
  constructor
  · intro ⟨hm, h1, h2, h3⟩
    exact ⟨hm, h1, h2, h3.1⟩
  · intro ⟨hm, h1, h2, h3⟩
    exact ⟨hm, h1, h2, h3, fun hd => by
      have h := Nat.dvd_one.mp hd
      have := h1.two_le
      omega⟩

/-- On the source domain the triple `p q r` is below `Y^(267/462)`, which is what makes the
rescaled variable `t = Y/(p q r)` exceed both `Y^(195/462)` and `α = Y^(16/135)`. -/
lemma triple_product_lt {Y : ℝ} {p q r : ℕ} (hY : 1 < Y) (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hrq : r < q) (hqp : q < p)
    (hpβ : (p : ℝ) ≤ Y ^ (89 / 462 - 0.00000001 : ℝ)) :
    ((p * q * r : ℕ) : ℝ) < Y ^ (267 / 462 : ℝ) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hY1 : (1 : ℝ) ≤ Y := hY.le
  set g : ℝ := 89 / 462 - 0.00000001 with hg
  have hgpos : (0 : ℝ) < Y ^ g := Real.rpow_pos_of_pos hY0 _
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr.pos
  have hqβ : (q : ℝ) < Y ^ g := lt_of_lt_of_le (by exact_mod_cast hqp) hpβ
  have hrβ : (r : ℝ) < Y ^ g := lt_trans (by exact_mod_cast hrq) hqβ
  have hcast : ((p * q * r : ℕ) : ℝ) = (p : ℝ) * (q : ℝ) * (r : ℝ) := by push_cast; ring
  rw [hcast]
  have h1 : (p : ℝ) * (q : ℝ) < (Y ^ g) * (Y ^ g) := by
    have ha : (p : ℝ) * (q : ℝ) ≤ (Y ^ g) * (q : ℝ) := mul_le_mul_of_nonneg_right hpβ hq0.le
    have hb : (Y ^ g) * (q : ℝ) < (Y ^ g) * (Y ^ g) := mul_lt_mul_of_pos_left hqβ hgpos
    linarith
  have h2 : (p : ℝ) * (q : ℝ) * (r : ℝ) < ((Y ^ g) * (Y ^ g)) * (Y ^ g) := by
    have ha : (p : ℝ) * (q : ℝ) * (r : ℝ) ≤ ((Y ^ g) * (Y ^ g)) * (r : ℝ) :=
      mul_le_mul_of_nonneg_right h1.le hr0.le
    have hb : ((Y ^ g) * (Y ^ g)) * (r : ℝ) < ((Y ^ g) * (Y ^ g)) * (Y ^ g) :=
      mul_lt_mul_of_pos_left hrβ (by positivity)
    linarith
  have h3 : ((Y ^ g) * (Y ^ g)) * (Y ^ g) = (Y ^ g) ^ (3 : ℕ) := by ring
  have h4 : (Y ^ g) ^ (3 : ℕ) = Y ^ (g * 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le]
    norm_num
  have h5 : g * 3 < 267 / 462 := by
    rw [hg]
    norm_num
  calc (p : ℝ) * (q : ℝ) * (r : ℝ) < ((Y ^ g) * (Y ^ g)) * (Y ^ g) := h2
    _ = (Y ^ g) ^ (3 : ℕ) := h3
    _ = Y ^ (g * 3) := h4
    _ < Y ^ (267 / 462 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hY h5

-- === the reciprocal triple sum ===
/-- The reciprocal triple sum over the source pair domain, bounded by an absolute constant. -/
lemma triple_domain_recip_le {Y : ℝ} {n : ℕ} (hY : 1 < Y)
    (hS : ∑ p ∈ (Icc ⌈Y ^ (16 / 135 : ℝ)⌉₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
            (fun p : ℕ => p.Prime), (1 : ℝ) / (p : ℝ)
          ≤ 2 * Real.log 4 * (1 / Real.log 2 + 1)) :
    ∑ pq ∈ pairDomain true Y n,
        ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
          Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
        1 / ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ))
      ≤ (2 * Real.log 4 * (1 / Real.log 2 + 1)) ^ 3 := by
  set α : ℝ := Y ^ (16 / 135 : ℝ) with hα
  set β : ℝ := Y ^ (89 / 462 - 0.00000001 : ℝ) with hβ
  set S : ℝ := 2 * Real.log 4 * (1 / Real.log 2 + 1) with hSdef
  set W : Finset ℕ := (Icc ⌈α⌉₊ ⌊β⌋₊).filter (fun p : ℕ => p.Prime) with hW
  have hWbound : ∑ w ∈ W, (1 : ℝ) / (w : ℝ) ≤ S := by
    rw [hW, hSdef]
    exact hS
  have hS0 : 0 ≤ S := by rw [hSdef]; positivity
  have hdom : ∀ pq ∈ pairDomain true Y n, pq.1.Prime ∧ α < (pq.1 : ℝ) ∧ pq.2.Prime ∧
      α < (pq.2 : ℝ) ∧ (pq.2 : ℝ) < (pq.1 : ℝ) ∧ (pq.1 : ℝ) ≤ β := by
    intro pq hpq
    rw [pairDomain, mem_filter] at hpq
    obtain ⟨hpr, hαp, hsp, hqr, hαq, hqmin, hgrp, hdec, hβp⟩ := hpq.2
    exact ⟨hpr, hαp, hqr, hαq, lt_of_lt_of_le hqmin (min_le_left _ _), hβp rfl⟩
  have hpmem : ∀ pq ∈ pairDomain true Y n, pq.1 ∈ W ∧ pq.2 ∈ W := by
    intro pq hpq
    obtain ⟨hpr, hαp, hqr, hαq, hqp, hβp⟩ := hdom pq hpq
    refine ⟨?_, ?_⟩
    · rw [hW]
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.ceil_le.mpr hαp.le, Nat.le_floor hβp⟩, hpr⟩
    · rw [hW]
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.ceil_le.mpr hαq.le, Nat.le_floor ?_⟩, hqr⟩
      exact le_of_lt (lt_of_lt_of_le hqp hβp)
  have hsub_r : ∀ pq ∈ pairDomain true Y n,
      (range (n + 1)).filter (fun r : ℕ => r.Prime ∧ α ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ))
        ⊆ W := by
    intro pq hpq r hr
    obtain ⟨-, -, -, -, hqp, hβp⟩ := hdom pq hpq
    obtain ⟨-, hrr, hαr, hrq⟩ := mem_filter.mp hr
    rw [hW]
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.ceil_le.mpr hαr, Nat.le_floor ?_⟩, hrr⟩
    exact le_of_lt (lt_trans hrq (lt_of_lt_of_le hqp hβp))
  have hstepA : ∀ pq ∈ pairDomain true Y n,
      ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧ α ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
        (1 : ℝ) / (r : ℝ) ≤ S := by
    intro pq hpq
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (hsub_r pq hpq)
      (fun x _ _ => by positivity)) hWbound
  have hstepB : ∑ pq ∈ pairDomain true Y n,
        ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧ α ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
        1 / ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ))
      = ∑ pq ∈ pairDomain true Y n, (1 / ((pq.1 : ℝ) * (pq.2 : ℝ))) *
          ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧ α ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
            (1 : ℝ) / (r : ℝ) := by
    refine Finset.sum_congr rfl (fun pq _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    field_simp
    try ring
  have hstepC : ∑ pq ∈ pairDomain true Y n, (1 / ((pq.1 : ℝ) * (pq.2 : ℝ))) *
        ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧ α ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
          (1 : ℝ) / (r : ℝ)
      ≤ ∑ pq ∈ pairDomain true Y n, (1 / ((pq.1 : ℝ) * (pq.2 : ℝ))) * S := by
    refine Finset.sum_le_sum (fun pq hpq => ?_)
    have hpos : (0 : ℝ) ≤ 1 / ((pq.1 : ℝ) * (pq.2 : ℝ)) := by
      obtain ⟨hpr, -, hqr, -, -, -⟩ := hdom pq hpq
      have h1 : (0 : ℝ) < (pq.1 : ℝ) := by exact_mod_cast hpr.pos
      have h2 : (0 : ℝ) < (pq.2 : ℝ) := by exact_mod_cast hqr.pos
      positivity
    exact mul_le_mul_of_nonneg_left (hstepA pq hpq) hpos
  have hpair : ∑ pq ∈ pairDomain true Y n, (1 / ((pq.1 : ℝ) * (pq.2 : ℝ))) ≤ S * S := by
    have hsubp : pairDomain true Y n ⊆ W ×ˢ W := by
      intro pq hpq
      exact mem_product.mpr (hpmem pq hpq)
    have h1 : ∑ pq ∈ pairDomain true Y n, (1 / ((pq.1 : ℝ) * (pq.2 : ℝ)))
        ≤ ∑ pq ∈ W ×ˢ W, (1 / ((pq.1 : ℝ) * (pq.2 : ℝ))) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubp (fun x _ _ => by positivity)
    have h2 : ∑ pq ∈ W ×ˢ W, (1 / ((pq.1 : ℝ) * (pq.2 : ℝ)))
        = (∑ p ∈ W, (1 : ℝ) / (p : ℝ)) * ∑ q ∈ W, (1 : ℝ) / (q : ℝ) := by
      rw [Finset.sum_product]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      simp only [Prod.fst, Prod.snd]
      field_simp
      try ring
    calc ∑ pq ∈ pairDomain true Y n, (1 / ((pq.1 : ℝ) * (pq.2 : ℝ)))
        ≤ ∑ pq ∈ W ×ˢ W, (1 / ((pq.1 : ℝ) * (pq.2 : ℝ))) := h1
      _ = (∑ p ∈ W, (1 : ℝ) / (p : ℝ)) * ∑ q ∈ W, (1 : ℝ) / (q : ℝ) := h2
      _ ≤ S * S := mul_le_mul hWbound hWbound (by positivity) hS0
  calc ∑ pq ∈ pairDomain true Y n,
        ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧ α ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
        1 / ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ))
      = ∑ pq ∈ pairDomain true Y n, (1 / ((pq.1 : ℝ) * (pq.2 : ℝ))) *
          ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧ α ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
            (1 : ℝ) / (r : ℝ) := hstepB
    _ ≤ ∑ pq ∈ pairDomain true Y n, (1 / ((pq.1 : ℝ) * (pq.2 : ℝ))) * S := hstepC
    _ = S * ∑ pq ∈ pairDomain true Y n, (1 / ((pq.1 : ℝ) * (pq.2 : ℝ))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun pq _ => by ring)
    _ ≤ S * (S * S) := mul_le_mul_of_nonneg_left hpair hS0
    _ = S ^ 3 := by ring

-- === the assembly ===
/-- Jia pages 284 and 285: the model triple count comparison assembled from Lemma 21, the
Lemma 20 constant branch, and the uniform reciprocal bound `C` for the domain. -/
lemma triple_mass_le_model {Y : ℝ} {n : ℕ} {w : ℝ → ℝ} {T0 Z0 η₁ C η : ℝ}
    (h20 : type_of% lemma20_global_bounds) (hw : ContinuousOn w (Set.Ici 1))
    (hi : ∀ u : ℝ, 1 ≤ u → u ≤ 2 → w u = 1 / u)
    (hrec : ∀ u : ℝ, 2 ≤ u → u * w u = 1 + ∫ t in (1 : ℝ)..(u - 1), w t)
    (h21 : ∀ t z : ℝ, T0 ≤ t → Z0 ≤ z → z ≤ t →
      |((sieved (Ioc ⌊t⌋₊ ⌊2 * t⌋₊) 1 z).card : ℝ) -
          w (Real.log t / Real.log z) * (t / Real.log z)| ≤ η₁ * (t / Real.log z))
    (hη₁ : 0 < η₁) (hη : 0 < η)
    (hbudget : η₁ * (135 / 16) * C ≤ η)
    (hC : ∑ pq ∈ pairDomain true Y n,
        ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
          Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
        1 / ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ)) ≤ C)
    (hY : 1 < Y) (hT : T0 ≤ Y ^ (195 / 462 : ℝ)) (hZ : Z0 ≤ Y ^ (16 / 135 : ℝ)) :
    tripleMass true true 0 Y n (Y ^ (16 / 135 : ℝ)) (Y ^ (16 / 135 : ℝ))
      ≤ (triplePrimeModel Y n + η) * (Y / Real.log Y) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  rw [tripleMass_eq_double_sum]
  set α : ℝ := Y ^ (16 / 135 : ℝ) with hαdef
  have hYα0 : (0 : ℝ) ≤ Y / Real.log α := by
    have hlogα : Real.log α = (16 / 135) * Real.log Y := by rw [hαdef, Real.log_rpow hY0]
    have : 0 < Real.log α := by rw [hlogα]; positivity
    positivity
  have hdom : ∀ pq ∈ pairDomain true Y n,
      pq.1.Prime ∧ α < (pq.1 : ℝ) ∧ pq.2.Prime ∧
        α < (pq.2 : ℝ) ∧ (pq.2 : ℝ) < (pq.1 : ℝ) ∧
        (pq.1 : ℝ) ≤ Y ^ (89 / 462 - 0.00000001 : ℝ) := by
    intro pq hpq
    rw [pairDomain, mem_filter] at hpq
    obtain ⟨hpr, hαp, hsp, hqr, hαq, hqmin, hgrp, hdec, hβp⟩ := hpq.2
    exact ⟨hpr, hαp, hqr, hαq, lt_of_lt_of_le hqmin (min_le_left _ _), hβp rfl⟩
  have hbig : ∀ pq ∈ pairDomain true Y n,
      ∀ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
        α ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
      Y ^ (195 / 462 : ℝ) < Y / ((pq.1 * pq.2 * r : ℕ) : ℝ) := by
    intro pq hpq r hr
    obtain ⟨hpr, hαp, hqr, hαq, hqp, hβp⟩ := hdom pq hpq
    obtain ⟨-, hrr, hαr, hrq⟩ := mem_filter.mp hr
    have hrq' : r < pq.2 := by exact_mod_cast hrq
    have hqp' : pq.2 < pq.1 := by exact_mod_cast hqp
    have hdlt := triple_product_lt hY hpr hqr hrr hrq' hqp' hβp
    have hdpos : (0 : ℝ) < ((pq.1 * pq.2 * r : ℕ) : ℝ) := by
      have h0 : 0 < pq.1 * pq.2 * r := Nat.mul_pos (Nat.mul_pos hpr.pos hqr.pos) hrr.pos
      exact_mod_cast h0
    have hαpos : (0 : ℝ) < Y ^ (195 / 462 : ℝ) := Real.rpow_pos_of_pos hY0 _
    rw [lt_div_iff₀ hdpos]
    have hsplit : Y = Y ^ (195 / 462 : ℝ) * Y ^ (267 / 462 : ℝ) := by
      rw [← Real.rpow_add hY0]
      norm_num
    conv_rhs => rw [hsplit]
    exact mul_lt_mul_of_pos_left hdlt hαpos
  have hterm : ∀ pq ∈ pairDomain true Y n,
      ∀ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
        α ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
      ((sieved ((sourceSet true 0 Y n (pq.1 * pq.2)).filter (fun a => r ∣ a)) 1 α).card : ℝ)
        ≤ (if (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then (0.5617 : ℝ) else 0.5644) *
            (Y / ((pq.1 * pq.2 * r : ℕ) : ℝ) / Real.log α)
          + η₁ * (Y / ((pq.1 * pq.2 * r : ℕ) : ℝ) / Real.log α) := by
    intro pq hpq r hr
    obtain ⟨hpr, hαp, hqr, hαq, hqp, hβp⟩ := hdom pq hpq
    obtain ⟨-, hrr, hαr, hrq⟩ := mem_filter.mp hr
    have hrq' : r < pq.2 := by exact_mod_cast hrq
    have hqp' : pq.2 < pq.1 := by exact_mod_cast hqp
    have hbig' := hbig pq hpq r hr
    have hzt : α ≤ Y / ((pq.1 * pq.2 * r : ℕ) : ℝ) := by
      refine le_trans ?_ hbig'.le
      rw [hαdef]
      exact Real.rpow_le_rpow_of_exponent_le hY.le (by norm_num : (16 / 135 : ℝ) ≤ 195 / 462)
    exact triple_term_le h20 hw hi hrec h21 hη₁ hpr hqr hrr hrq' hqp' hY hαp hβp
      (le_trans hT hbig'.le) hZ hzt
  have hstep1 : ∑ pq ∈ pairDomain true Y n,
        ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
          α ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
          ((sieved ((sourceSet true 0 Y n (pq.1 * pq.2)).filter (fun a => r ∣ a)) 1 α).card : ℝ)
      ≤ ∑ pq ∈ pairDomain true Y n,
        ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
          α ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
          ((if (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then (0.5617 : ℝ) else 0.5644) *
              (Y / ((pq.1 * pq.2 * r : ℕ) : ℝ) / Real.log α)
            + η₁ * (Y / ((pq.1 * pq.2 * r : ℕ) : ℝ) / Real.log α)) :=
    Finset.sum_le_sum (fun pq hpq => Finset.sum_le_sum (fun r hr => hterm pq hpq r hr))
  have hstep2 : ∑ pq ∈ pairDomain true Y n,
        ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
          α ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
          ((if (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then (0.5617 : ℝ) else 0.5644) *
              (Y / ((pq.1 * pq.2 * r : ℕ) : ℝ) / Real.log α)
            + η₁ * (Y / ((pq.1 * pq.2 * r : ℕ) : ℝ) / Real.log α))
      = (Y / Real.log α) * ∑ pq ∈ pairDomain true Y n,
        ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
          α ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
          ((if (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then (0.5617 : ℝ) else 0.5644) + η₁) /
            ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun pq _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    have hcast : ((pq.1 * pq.2 * r : ℕ) : ℝ) = (pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ) := by
      push_cast; ring
    rw [hcast]
    field_simp
    try ring
  have hstep3 : ∑ pq ∈ pairDomain true Y n,
        ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
          α ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
          ((if (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then (0.5617 : ℝ) else 0.5644) + η₁) /
            ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ))
      = (∑ pq ∈ pairDomain true Y n,
            ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
              α ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
              (if (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then (0.5617 : ℝ) else 0.5644) /
                ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ)))
        + η₁ * (∑ pq ∈ pairDomain true Y n,
            ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
              α ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
              1 / ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ))) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun pq _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    field_simp
    try ring
  have hmodel : (∑ pq ∈ pairDomain true Y n,
        ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
          α ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
          (if (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then (0.5617 : ℝ) else 0.5644) /
            ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ)))
      = triplePrimeModel Y n * (16 / 135) := by
    have hdef : triplePrimeModel Y n = (135 / 16) * ∑ pq ∈ pairDomain true Y n,
        ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
          α ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
          (if (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then (0.5617 : ℝ) else 0.5644) /
            ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ)) := rfl
    rw [hdef]
    ring
  have hYα : Y / Real.log α = (135 / 16) * (Y / Real.log Y) := by
    have hlogα : Real.log α = (16 / 135) * Real.log Y := by rw [hαdef, Real.log_rpow hY0]
    rw [hlogα]
    field_simp
    try ring
  have hYY : (0 : ℝ) ≤ Y / Real.log Y := by positivity
  calc ∑ pq ∈ pairDomain true Y n,
          ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
            α ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
            ((sieved ((sourceSet true 0 Y n (pq.1 * pq.2)).filter (fun a => r ∣ a)) 1 α).card : ℝ)
      ≤ ∑ pq ∈ pairDomain true Y n,
        ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
          α ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
          ((if (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then (0.5617 : ℝ) else 0.5644) *
              (Y / ((pq.1 * pq.2 * r : ℕ) : ℝ) / Real.log α)
            + η₁ * (Y / ((pq.1 * pq.2 * r : ℕ) : ℝ) / Real.log α)) := hstep1
    _ = (Y / Real.log α) * ∑ pq ∈ pairDomain true Y n,
          ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
            α ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
            ((if (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then (0.5617 : ℝ) else 0.5644) + η₁) /
              ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ)) := hstep2
    _ = (Y / Real.log α) * ((∑ pq ∈ pairDomain true Y n,
            ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
              α ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
              (if (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then (0.5617 : ℝ) else 0.5644) /
                ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ)))
        + η₁ * (∑ pq ∈ pairDomain true Y n,
            ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
              α ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
              1 / ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ)))) := by rw [hstep3]
    _ ≤ (Y / Real.log α) * (triplePrimeModel Y n * (16 / 135) + η₁ * C) := by
        refine mul_le_mul_of_nonneg_left ?_ hYα0
        rw [hmodel]
        have hml := mul_le_mul_of_nonneg_left hC hη₁.le
        linarith
    _ ≤ (triplePrimeModel Y n + η) * (Y / Real.log Y) := by
        rw [hYα]
        have heq : (135 / 16) * (Y / Real.log Y) *
              (triplePrimeModel Y n * (16 / 135) + η₁ * C)
            = triplePrimeModel Y n * (Y / Real.log Y) + η₁ * (135 / 16) * C * (Y / Real.log Y) := by
          ring
        rw [heq]
        have hb : η₁ * (135 / 16) * C * (Y / Real.log Y) ≤ η * (Y / Real.log Y) :=
          mul_le_mul_of_nonneg_right hbudget hYY
        have hfin : triplePrimeModel Y n * (Y / Real.log Y) + η * (Y / Real.log Y)
            = (triplePrimeModel Y n + η) * (Y / Real.log Y) := by ring
        linarith

/-- LEAF. Jia page 284 after display 63, the model triple count to prime sum comparison.
CONDITIONAL ON the unchanged explicit solution, Lemma 20 and Lemma 21 inputs.
The global argument ranges are Geometry565.triple_four_argument and
Geometry565.triple_three_region1_argument. Only individual rough counts are replaced. -/
theorem triple_rough_upper
    (hex : type_of% buchstab_solution)
    (h20 : type_of% lemma20_global_bounds)
    (h21 : type_of% lemma21_rough_asymptotic) :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∀ n : ℕ, 2 * Y ≤ (n : ℝ) →
        tripleMass true true 0 Y n (Y ^ (16 / 135 : ℝ)) (Y ^ (16 / 135 : ℝ)) ≤
          (triplePrimeModel Y n + η) * (Y / log Y) := by
  intro η hη
  obtain ⟨w, hw, hi, hrec⟩ := hex
  set C : ℝ := (2 * Real.log 4 * (1 / Real.log 2 + 1)) ^ 3 with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  have hC1 : 0 < C + 1 := by linarith
  set η₁ : ℝ := η / ((135 / 16) * (C + 1)) with hη₁def
  have hη₁ : 0 < η₁ := by rw [hη₁def]; positivity
  obtain ⟨T0, Z0, hT0, hZ0, h21'⟩ := h21 w hw hi hrec η₁ hη₁
  have hbudget : η₁ * (135 / 16) * C ≤ η := by
    have h1 : η₁ * (135 / 16) = η / (C + 1) := by
      rw [hη₁def]
      field_simp
    have h2 : η / (C + 1) * C ≤ η := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hC1]
      exact mul_le_mul_of_nonneg_left (by linarith : C ≤ C + 1) hη.le
    rw [h1]
    exact h2
  refine ⟨max 4 (max (Real.exp (135 / 16)) (max (T0 ^ (462 / 195 : ℝ) + 1)
    (Z0 ^ (135 / 16 : ℝ) + 1))), ?_⟩
  intro Y hYle n hn
  have hY4 : 4 ≤ Y := le_trans (le_max_left _ _) hYle
  have hY : 1 < Y := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hexp_le : Real.exp (135 / 16) ≤ Y :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hYle)
  have hT0le : T0 ^ (462 / 195 : ℝ) + 1 ≤ Y :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hYle))
  have hZ0le : Z0 ^ (135 / 16 : ℝ) + 1 ≤ Y :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hYle))
  have hT : T0 ≤ Y ^ (195 / 462 : ℝ) := by
    have hT0pos : (0 : ℝ) < T0 := by linarith
    have h1 : T0 ^ (462 / 195 : ℝ) ≤ Y := by linarith [hT0le]
    have h2 : (T0 ^ (462 / 195 : ℝ)) ^ (195 / 462 : ℝ) ≤ Y ^ (195 / 462 : ℝ) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hT0pos.le _) h1 (by norm_num)
    rw [← Real.rpow_mul hT0pos.le, show (462 / 195 : ℝ) * (195 / 462) = 1 by norm_num,
      Real.rpow_one] at h2
    exact h2
  have hZ : Z0 ≤ Y ^ (16 / 135 : ℝ) := by
    have hZ0pos : (0 : ℝ) < Z0 := by linarith
    have h1 : Z0 ^ (135 / 16 : ℝ) ≤ Y := by linarith [hZ0le]
    have h2 : (Z0 ^ (135 / 16 : ℝ)) ^ (16 / 135 : ℝ) ≤ Y ^ (16 / 135 : ℝ) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hZ0pos.le _) h1 (by norm_num)
    rw [← Real.rpow_mul hZ0pos.le, show (135 / 16 : ℝ) * (16 / 135) = 1 by norm_num,
      Real.rpow_one] at h2
    exact h2
  have hlogα : 1 ≤ Real.log (Y ^ (16 / 135 : ℝ)) := by
    rw [Real.log_rpow hY0]
    have h2 : 135 / 16 ≤ Real.log Y := by
      have h3 := Real.log_le_log (Real.exp_pos (135 / 16)) hexp_le
      rwa [Real.log_exp] at h3
    nlinarith
  have hα1 : 1 < Y ^ (16 / 135 : ℝ) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (16 / 135 : ℝ) := (Real.one_rpow _).symm
      _ < Y ^ (16 / 135 : ℝ) := Real.rpow_lt_rpow (by norm_num) hY (by norm_num)
  have hαβ : Y ^ (16 / 135 : ℝ) ≤ Y ^ (89 / 462 - 0.00000001 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hY.le (by norm_num)
  have hrat : Real.log (Y ^ (89 / 462 - 0.00000001 : ℝ)) ≤
      2 * Real.log (Y ^ (16 / 135 : ℝ)) := by
    have h1 : Real.log (Y ^ (89 / 462 - 0.00000001 : ℝ)) =
        (89 / 462 - 0.00000001) * Real.log Y := Real.log_rpow hY0 _
    have h2 : Real.log (Y ^ (16 / 135 : ℝ)) = (16 / 135) * Real.log Y := Real.log_rpow hY0 _
    rw [h1, h2]
    nlinarith [Real.log_pos hY]
  have hSw := sum_inv_primes_window_le (X := Y ^ (16 / 135 : ℝ))
    (Z := Y ^ (89 / 462 - 0.00000001 : ℝ)) hα1 hαβ hlogα hrat
  have hCbound : ∑ pq ∈ pairDomain true Y n,
        ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
          Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)),
        1 / ((pq.1 : ℝ) * (pq.2 : ℝ) * (r : ℝ)) ≤ C := by
    rw [hCdef]
    exact triple_domain_recip_le hY hSw
  exact triple_mass_le_model (w := w) (T0 := T0) (Z0 := Z0) (η₁ := η₁) (C := C) (η := η)
    h20 hw hi hrec h21' hη₁ hη hbudget hCbound hY hT hZ


namespace WIP

set_option maxHeartbeats 2000000
open Real Finset intervalIntegral
open LeanLab.PNTSieve.Mertens
open LeanLab.Languasco2004.Numeric565
open Real Finset intervalIntegral
open Decomp578c Decomp578d
open LeanLab.PNTSieve.Mertens
noncomputable section

/-- `log ⌈Y^x⌉₊` sits between `x log Y` and `x log Y + log 2`. -/
private theorem log_ceil_sandwich {Y x : ℝ} (hY : 1 < Y) (hx : 0 < x) :
    0 ≤ Real.log (⌈Y ^ x⌉₊ : ℝ) - x * Real.log Y ∧
      Real.log (⌈Y ^ x⌉₊ : ℝ) - x * Real.log Y ≤ Real.log 2 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hxp : (1 : ℝ) < Y ^ x := Real.one_lt_rpow hY hx
  have hpos : (0 : ℝ) < ((⌈Y ^ x⌉₊ : ℕ) : ℝ) := by
    have h := Nat.le_ceil (Y ^ x)
    linarith
  constructor
  · have h : Real.log (Y ^ x) ≤ Real.log ((⌈Y ^ x⌉₊ : ℕ) : ℝ) :=
      Real.log_le_log (Real.rpow_pos_of_pos hY0 x) (Nat.le_ceil _)
    rw [Real.log_rpow hY0] at h
    linarith
  · have h2 : ((⌈Y ^ x⌉₊ : ℕ) : ℝ) ≤ 2 * Y ^ x := by
      have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ Y ^ x by positivity)
      have h1 : (1 : ℝ) ≤ Y ^ x := le_of_lt hxp
      linarith
    calc Real.log ((⌈Y ^ x⌉₊ : ℕ) : ℝ) - x * Real.log Y
        ≤ Real.log (2 * Y ^ x) - x * Real.log Y := by
          have h := Real.log_le_log hpos h2
          linarith
      _ = Real.log 2 := by
          rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hY0 x)),
            Real.log_rpow hY0]
          ring

/-- `log ⌊Y^x⌋₊` sits within `log 2` of `x log Y` once `Y^x ≥ 2`. -/
private theorem log_floor_sandwich {Y x : ℝ} (hY : 1 < Y) (h2 : 2 ≤ Y ^ x) :
    |Real.log ((⌊Y ^ x⌋₊ : ℕ) : ℝ) - x * Real.log Y| ≤ Real.log 2 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hfx : (0 : ℝ) < Y ^ x := lt_of_lt_of_le (by norm_num) h2
  have hle : ((⌊Y ^ x⌋₊ : ℕ) : ℝ) ≤ Y ^ x := Nat.floor_le (by linarith)
  have hge : Y ^ x / 2 ≤ ((⌊Y ^ x⌋₊ : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one (Y ^ x)
    linarith
  have hpos : (0 : ℝ) < ((⌊Y ^ x⌋₊ : ℕ) : ℝ) := by linarith
  rw [abs_le]
  constructor
  · have h1 : Real.log (Y ^ x / 2) ≤ Real.log ((⌊Y ^ x⌋₊ : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) hge
    have he : Real.log (Y ^ x / 2) = x * Real.log Y - Real.log 2 := by
      rw [Real.log_div (ne_of_gt hfx) (by norm_num), Real.log_rpow hY0]
    linarith
  · have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h1 : Real.log ((⌊Y ^ x⌋₊ : ℕ) : ℝ) ≤ Real.log (Y ^ x) :=
      Real.log_le_log hpos hle
    rw [Real.log_rpow hY0] at h1
    linarith

/-- The log-log difference of a real prime window equals `log (x2/x1)` up to `O(1/(x1 log Y))`. -/
private theorem loglog_window {Y x1 x2 : ℝ} (hY : 1 < Y) (hx1 : 0 < x1) (hx12 : x1 ≤ x2)
    (hbig : 2 * Real.log 2 ≤ x1 * Real.log Y)
    (hy2 : 2 ≤ ⌈Y ^ x1⌉₊) (hw2 : 2 ≤ ⌊Y ^ x2⌋₊) :
    |(Real.log (Real.log ((⌊Y ^ x2⌋₊ : ℕ) : ℝ)) - Real.log (Real.log ((⌈Y ^ x1⌉₊ : ℕ) : ℝ)))
      - Real.log (x2 / x1)| ≤ 4 * Real.log 2 / (x1 * Real.log Y) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨hAc1, hAc2⟩ := log_ceil_sandwich hY hx1
  have hx2pos : 0 < x2 := lt_of_lt_of_le hx1 hx12
  have hA2le : x1 * Real.log Y ≤ x2 * Real.log Y := by
    exact mul_le_mul_of_nonneg_right hx12 hlogY.le
  have hx2big : 2 * Real.log 2 ≤ x2 * Real.log Y := le_trans hbig hA2le
  obtain ⟨hFc1, hFc2⟩ := (abs_le.mp (log_floor_sandwich (Y := Y) (x := x2) hY
      (le_trans (by exact_mod_cast hw2) (Nat.floor_le (by positivity)))))
  -- upper endpoint
  set A2 := x2 * Real.log Y with hA2
  set A1 := x1 * Real.log Y with hA1
  have hA2pos : 0 < A2 := by positivity
  have hA1pos : 0 < A1 := by positivity
  set B2 := Real.log ((⌊Y ^ x2⌋₊ : ℕ) : ℝ) with hB2
  set B1 := Real.log ((⌈Y ^ x1⌉₊ : ℕ) : ℝ) with hB1
  have hB2pos : 0 < B2 := by
    rw [hB2]
    apply Real.log_pos
    have h2 : (2 : ℝ) ≤ ((⌊Y ^ x2⌋₊ : ℕ) : ℝ) := by exact_mod_cast hw2
    linarith
  have hB1pos : 0 < B1 := by
    rw [hB1]
    apply Real.log_pos
    have h2 : (2 : ℝ) ≤ ((⌈Y ^ x1⌉₊ : ℕ) : ℝ) := by exact_mod_cast hy2
    linarith
  have hhi1 : B1 / A1 - 1 ≤ Real.log 2 / A1 := by
    have he : B1 / A1 - 1 = (B1 - A1) / A1 := by field_simp
    rw [he]
    exact div_le_div_of_nonneg_right hAc2 hA1pos.le
  have hb2le : B2 ≤ A2 := by
    have hle : ((⌊Y ^ x2⌋₊ : ℕ) : ℝ) ≤ Y ^ x2 := Nat.floor_le (by positivity)
    have h1 : Real.log ((⌊Y ^ x2⌋₊ : ℕ) : ℝ) ≤ Real.log (Y ^ x2) :=
      Real.log_le_log (by positivity) hle
    rw [Real.log_rpow hY0] at h1
    simpa only [hB2, hA2] using h1
  have hu2 : B2 / A2 ≤ 1 := by rw [div_le_one hA2pos]; exact hb2le
  have hu1 : 1 ≤ B1 / A1 := by
    rw [le_div_iff₀ hA1pos]
    linarith
  have hAA : Real.log (x2 / x1) = Real.log A2 - Real.log A1 := by
    rw [← Real.log_div (ne_of_gt hA2pos) (ne_of_gt hA1pos)]
    congr 1
    rw [hA2, hA1]
    field_simp
  have hkey : Real.log B2 - Real.log B1 - Real.log (x2 / x1) =
      Real.log (B2 / A2) - Real.log (B1 / A1) := by
    rw [hAA, Real.log_div (ne_of_gt hB2pos) (ne_of_gt hA2pos),
      Real.log_div (ne_of_gt hB1pos) (ne_of_gt hA1pos)]
    ring
  have hL2 : |Real.log (B2 / A2)| ≤ 2 * Real.log 2 / A2 := by
    have hpos2 : 0 < B2 / A2 := div_pos hB2pos hA2pos
    have hneg : Real.log (B2 / A2) ≤ 0 := Real.log_nonpos hpos2.le hu2
    have hinv : Real.log (B2 / A2) = - Real.log (A2 / B2) := by
      rw [← Real.log_inv]
      congr 1
      rw [inv_div]
    rw [abs_of_nonpos hneg, hinv, neg_neg]
    have hstep : Real.log (A2 / B2) ≤ A2 / B2 - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hA2pos hB2pos)
    have heq : A2 / B2 - 1 = (A2 - B2) / B2 := by field_simp
    have hnum : A2 - B2 ≤ Real.log 2 := by linarith
    have hB2half : A2 / 2 ≤ B2 := by linarith
    have hfin : (A2 - B2) / B2 ≤ 2 * Real.log 2 / A2 := by
      rw [div_le_div_iff₀ hB2pos hA2pos]
      nlinarith
    rw [heq] at hstep
    linarith
  have hL1 : |Real.log (B1 / A1)| ≤ Real.log 2 / A1 := by
    have hpos1 : 0 < B1 / A1 := div_pos hB1pos hA1pos
    rw [abs_of_nonneg (Real.log_nonneg hu1)]
    exact le_trans (Real.log_le_sub_one_of_pos hpos1) hhi1
  rw [hkey]
  have hfin : |Real.log (B2 / A2) - Real.log (B1 / A1)| ≤
      2 * Real.log 2 / A2 + Real.log 2 / A1 := by
    have hab : |Real.log (B2 / A2) - Real.log (B1 / A1)|
        = |Real.log (B2 / A2) + (- Real.log (B1 / A1))| := by
      rw [sub_eq_add_neg]
    rw [hab]
    calc |Real.log (B2 / A2) + (- Real.log (B1 / A1))|
        ≤ |Real.log (B2 / A2)| + |- Real.log (B1 / A1)| := abs_add_le _ _
      _ = |Real.log (B2 / A2)| + |Real.log (B1 / A1)| := by rw [abs_neg]
      _ ≤ 2 * Real.log 2 / A2 + Real.log 2 / A1 := by linarith
  have htail : 2 * Real.log 2 / A2 + Real.log 2 / A1 ≤
      4 * Real.log 2 / (x1 * Real.log Y) := by
    have hle1 : 2 * Real.log 2 / A2 ≤ 2 * Real.log 2 / A1 :=
      div_le_div_of_nonneg_left (by positivity) hA1pos hA2le
    have hsplit : 2 * Real.log 2 / A1 + Real.log 2 / A1 = 3 * Real.log 2 / A1 := by ring
    have h3 : 3 * Real.log 2 / A1 ≤ 4 * Real.log 2 / (x1 * Real.log Y) := by
      rw [hA1]
      have hpos : 0 < x1 * Real.log Y := by positivity
      exact div_le_div_of_nonneg_right (by linarith : (3:ℝ) * Real.log 2 ≤ 4 * Real.log 2) hpos.le
    linarith
  exact le_trans hfin htail

/-- Uniform two-sided Mertens deviation on a real prime window:
`Σ_{Y^x1 < p ≤ Y^x2} 1/p = log (x2/x1) + O(1/(x1 log Y))`. -/
private theorem prime_window_deviation {Y x1 x2 : ℝ} (hY : 1 < Y)
    (hx1 : 0 < x1) (hx12 : x1 ≤ x2)
    (hx1a : 16 / 135 ≤ x1) (hx2b : x2 ≤ 89 / 462 - 0.00000001)
    (hbig : 2 * Real.log 2 ≤ x1 * Real.log Y)
    (hne : ⌈Y ^ x1⌉₊ ≤ ⌊Y ^ x2⌋₊) :
    |(∑ p ∈ (Ioc ⌈Y ^ x1⌉₊ ⌊Y ^ x2⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
        - Real.log (x2 / x1)| ≤ 40 * Real.log 2 / (x1 * Real.log Y) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2half : (1 / 2 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hl2one : Real.log 2 < 1 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    linarith [Real.exp_one_gt_d9]
  have hx1Y : 0 < x1 * Real.log Y := by positivity
  have hxp1 : (1 : ℝ) < Y ^ x1 := Real.one_lt_rpow hY hx1
  have hx2pos : 0 < x2 := lt_of_lt_of_le hx1 hx12
  have hxp2 : (2 : ℝ) ≤ Y ^ x2 := by
    have h2 : Real.log 2 ≤ Real.log Y * x2 := by
      have h3 := mul_le_mul_of_nonneg_right hx12 hlogY.le
      nlinarith [hbig, h3]
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log Y * x2) := Real.exp_le_exp.mpr h2
      _ = Y ^ x2 := (Real.rpow_def_of_pos hY0 x2).symm
  -- set notation
  set y0 : ℕ := ⌈Y ^ x1⌉₊ with hy0def
  set w : ℕ := ⌊Y ^ x2⌋₊ with hwdef
  have hy02 : 2 ≤ y0 := by
    have h : (1 : ℝ) < (y0 : ℝ) := by
      rw [hy0def]
      exact lt_of_lt_of_le hxp1 (Nat.le_ceil _)
    have h1 : (1 : ℕ) < y0 := by exact_mod_cast h
    omega
  have hw2 : 2 ≤ w := by
    rw [hwdef]
    exact Nat.le_floor hxp2
  have hy0w : y0 ≤ w := by
    rw [hy0def, hwdef]
    exact hne
  have hlogy0 : 0 < Real.log (y0 : ℝ) := by
    apply Real.log_pos
    have : (1 : ℝ) < (y0 : ℝ) := by exact_mod_cast (show 1 < y0 by omega)
    linarith
  have hlogy0big : x1 * Real.log Y ≤ Real.log (y0 : ℝ) := by
    have h := Nat.le_ceil (Y ^ x1)
    rw [← hy0def] at h
    have h1 : Real.log (Y ^ x1) ≤ Real.log (y0 : ℝ) :=
      Real.log_le_log (Real.rpow_pos_of_pos hY0 x1) h
    rw [Real.log_rpow hY0] at h1
    linarith
  have hE := Decomp588d.E_block_eq y0 w hy0w
  obtain ⟨hbL, hbU⟩ := Decomp588d.reciprocal_block_bounds y0 w hy02 hy0w
  set Λ : ℝ := Real.log (Real.log (w : ℝ)) - Real.log (Real.log (y0 : ℝ)) with hΛ
  rw [← hE]
  -- deviation of Λ from log (x2/x1)
  have hΛdev : |Λ - Real.log (x2 / x1)| ≤ 4 * Real.log 2 / (x1 * Real.log Y) := by
    have := loglog_window (Y := Y) (x1 := x1) (x2 := x2) hY hx1 hx12 hbig hy02 hw2
    simpa only [hΛ, hy0def, hwdef] using this
  -- |Λ| is bounded by 2 on the model ranges
  have hΛabs : |Λ| ≤ 3 := by
    have hratio : x2 / x1 ≤ 2 := by
      rw [div_le_iff₀ hx1]
      nlinarith [hx1a, hx2b]
    have h1 : Real.log (x2 / x1) ≤ 1 := by
      have hp : 0 < x2 / x1 := div_pos hx2pos hx1
      calc Real.log (x2 / x1) ≤ x2 / x1 - 1 := Real.log_le_sub_one_of_pos hp
        _ ≤ 1 := by linarith
    have hlog0 : 0 ≤ Real.log (x2 / x1) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hx1]
      linarith
    have h3 : |Λ - Real.log (x2 / x1)| ≤ 2 := by
      have h4 : 4 * Real.log 2 / (x1 * Real.log Y) ≤ 2 := by
        rw [div_le_iff₀ hx1Y]
        nlinarith [hbig, hl2]
      linarith [hΛdev, h4]
    rw [abs_le] at h3 ⊢
    constructor <;> linarith [h3.1, h3.2, h1, hlog0]
  have hden : 0 < Real.log (y0 : ℝ) + Real.log 2 := by linarith
  have hfac : Real.log (y0 : ℝ) / (Real.log (y0 : ℝ) + Real.log 2) =
      1 - Real.log 2 / (Real.log (y0 : ℝ) + Real.log 2) := by
    field_simp
    ring
  have hdev2 : |(E w - E y0) - Λ| ≤ 18 / (x1 * Real.log Y) := by
    have hlow : Λ - (Real.log 2 / (Real.log (y0 : ℝ) + Real.log 2)) * Λ -
        14 / Real.log (y0 : ℝ) ≤ E w - E y0 := by
      rw [hfac] at hbL
      nlinarith [hbL]
    have hup : E w - E y0 ≤ Λ + 14 / Real.log (y0 : ℝ) := hbU
    have hd : Real.log 2 / (Real.log (y0 : ℝ) + Real.log 2) ≤ 1 / (x1 * Real.log Y) := by
      rw [div_le_iff₀ hden]
      have hD : Real.log 2 ≤ (Real.log (y0 : ℝ) + Real.log 2) / (x1 * Real.log Y) := by
        rw [le_div_iff₀ hx1Y]
        have hprod2 : Real.log 2 * (x1 * Real.log Y) ≤ 1 * (x1 * Real.log Y) :=
          mul_le_mul_of_nonneg_right hl2one.le hx1Y.le
        linarith [hprod2, hlogy0big]
      calc Real.log 2 ≤ (Real.log (y0 : ℝ) + Real.log 2) / (x1 * Real.log Y) := hD
        _ = 1 / (x1 * Real.log Y) * (Real.log (y0 : ℝ) + Real.log 2) := by ring
    have hd0 : 0 ≤ Real.log 2 / (Real.log (y0 : ℝ) + Real.log 2) := by positivity
    have hprod : (Real.log 2 / (Real.log (y0 : ℝ) + Real.log 2)) * |Λ| ≤
        3 / (x1 * Real.log Y) := by
      calc (Real.log 2 / (Real.log (y0 : ℝ) + Real.log 2)) * |Λ|
          ≤ (1 / (x1 * Real.log Y)) * 3 := by
            apply mul_le_mul hd hΛabs (abs_nonneg _) (by positivity)
        _ = 3 / (x1 * Real.log Y) := by field_simp
    have hinv14 : 14 / Real.log (y0 : ℝ) ≤ 14 / (x1 * Real.log Y) :=
      div_le_div_of_nonneg_left (by norm_num) hx1Y hlogy0big
    have hA : Real.log 2 / (Real.log (y0 : ℝ) + Real.log 2) * Λ ≤ 3 / (x1 * Real.log Y) :=
      le_trans (mul_le_mul_of_nonneg_left (le_abs_self Λ) hd0) hprod
    have hlow' : Λ - 14 / Real.log (y0 : ℝ) - 3 / (x1 * Real.log Y) ≤ E w - E y0 := by
      linarith [hlow, hA]
    have hup' : E w - E y0 ≤ Λ + 14 / (x1 * Real.log Y) := by linarith [hup, hinv14]
    have hl2' : Λ - 14 * (Real.log (y0 : ℝ))⁻¹ - 3 * (x1 * Real.log Y)⁻¹ ≤ E w - E y0 := by
      simpa only [div_eq_mul_inv] using hlow'
    have hi14' : 14 * (Real.log (y0 : ℝ))⁻¹ ≤ 14 * (x1 * Real.log Y)⁻¹ := by
      have h := hinv14
      rw [div_eq_mul_inv, div_eq_mul_inv] at h
      exact h
    have hu' : E w - E y0 ≤ Λ + 14 * (x1 * Real.log Y)⁻¹ := by
      simpa only [div_eq_mul_inv] using hup'
    rw [abs_le]
    constructor
    · simp only [div_eq_mul_inv]
      linarith [hl2', hi14']
    · simp only [div_eq_mul_inv]
      linarith [hu']
  have htot : |(E w - E y0) - Real.log (x2 / x1)| ≤ 40 * Real.log 2 / (x1 * Real.log Y) := by
    have h1 : 18 / (x1 * Real.log Y) + 4 * Real.log 2 / (x1 * Real.log Y) ≤
        40 * Real.log 2 / (x1 * Real.log Y) := by
      rw [← add_div, div_le_div_iff_of_pos_right hx1Y]
      linarith [hl2half]
    calc |(E w - E y0) - Real.log (x2 / x1)|
        = |((E w - E y0) - Λ) + (Λ - Real.log (x2 / x1))| := by ring_nf
      _ ≤ |(E w - E y0) - Λ| + |Λ - Real.log (x2 / x1)| := abs_add_le _ _
      _ ≤ 18 / (x1 * Real.log Y) + 4 * Real.log 2 / (x1 * Real.log Y) := by
          linarith [hdev2, hΛdev]
      _ ≤ 40 * Real.log 2 / (x1 * Real.log Y) := h1
  simpa only [hy0def, hwdef] using htot


-- === the band decomposition of the model double integral ===
/-- On the model range the inner cap `min x ((71/135-x)/2)` is `x` up to `71/405`. -/
private theorem min_cap_eq {x : ℝ} :
    min x ((71 / 135 - x) / 2) = if x ≤ 71 / 405 then x else (71 / 135 - x) / 2 := by
  by_cases h : x ≤ 71 / 405
  · rw [if_pos h, min_eq_left]
    nlinarith
  · rw [if_neg h, min_eq_right]
    push_neg at h
    nlinarith

/-- The cap's logarithm is the `tripleTwo` integrand's logarithm. -/
private theorem cap_log_eq (x : ℝ) :
    Real.log ((71 / 135 - x) / 2 / (16 / 135)) = Real.log ((135 / 32) * (71 / 135 - x)) := by
  congr 1
  field_simp
  ring

/-- The capped logarithmic square is interval integrable on any subinterval of the model range. -/
private theorem band_integrable {u v : ℝ} (h1 : 16 / 135 ≤ u)
    (h2 : v ≤ 89 / 462 - 0.00000001) (huv : u ≤ v) :
    IntervalIntegrable
      (fun x : ℝ => (1 / 2) * Real.log (min x ((71 / 135 - x) / 2) / (16 / 135)) ^ 2 / x)
      MeasureTheory.volume u v := by
  apply ContinuousOn.intervalIntegrable_of_Icc huv
  have hpos : ∀ x ∈ Set.Icc u v, (0 : ℝ) < min x ((71 / 135 - x) / 2) / (16 / 135) := by
    intro x hx
    have hx1 : (16 / 135 : ℝ) ≤ x := le_trans h1 hx.1
    have hx2 : x ≤ 89 / 462 - 0.00000001 := le_trans hx.2 h2
    have hminlow : (16 / 135 : ℝ) ≤ min x ((71 / 135 - x) / 2) :=
      le_min hx1 (by linarith)
    apply div_pos (lt_of_lt_of_le (by norm_num : (0:ℝ) < 16/135) hminlow)
    norm_num
  have hne : ∀ x ∈ Set.Icc u v, min x ((71 / 135 - x) / 2) / (16 / 135) ≠ 0 := by
    intro x hx
    exact ne_of_gt (hpos x hx)
  have hxne : ∀ x ∈ Set.Icc u v, x ≠ 0 := by
    intro x hx
    have : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) (le_trans h1 hx.1)
    linarith
  have hminc : Continuous (fun x : ℝ => min x ((71 / 135 - x) / 2)) :=
    Continuous.min continuous_id (continuous_const.sub continuous_id |>.div_const 2)
  have hlog : ContinuousOn (fun x : ℝ => Real.log (min x ((71 / 135 - x) / 2) / (16 / 135)))
      (Set.Icc u v) := by
    apply ContinuousOn.log _ hne
    exact (hminc.continuousOn.div_const _)
  have hsq : ContinuousOn
      (fun x : ℝ => (1 / 2) * Real.log (min x ((71 / 135 - x) / 2) / (16 / 135)) ^ 2)
      (Set.Icc u v) := by
    exact continuousOn_const.mul (hlog.pow 2)
  exact hsq.div continuousOn_id hxne

/-- `tripleOne + tripleTwo`, i.e. the region `p q² ≤ Y^(71/135)`: the capped double integral
splits exactly at `71/405` into the two `Numeric565` pieces. -/
private theorem triple_band_integral {μ : ℝ} (hμ1 : 71 / 405 ≤ μ)
    (hμ2 : μ ≤ 89 / 462 - 0.00000001) :
    (∫ x in (16 / 135)..μ,
        (1 / 2) * Real.log (min x ((71 / 135 - x) / 2) / (16 / 135)) ^ 2 / x)
      = (1 / 2) * (∫ x in (16 / 135)..(71 / 405), Real.log (x / (16 / 135)) ^ 2 / x)
        + (1 / 2) * (∫ x in (71 / 405)..μ, Real.log ((135 / 32) * (71 / 135 - x)) ^ 2 / x) := by
  have hI1 := band_integrable (u := 16 / 135) (v := 71 / 405)
    (le_refl _) (by norm_num) (by norm_num)
  have hI2 := band_integrable (u := 71 / 405) (v := μ)
    (by norm_num) hμ2 hμ1
  have hsplit :
      (∫ x in (16 / 135)..(71 / 405),
          (1 / 2) * Real.log (min x ((71 / 135 - x) / 2) / (16 / 135)) ^ 2 / x)
        + (∫ x in (71 / 405)..μ,
          (1 / 2) * Real.log (min x ((71 / 135 - x) / 2) / (16 / 135)) ^ 2 / x)
      = ∫ x in (16 / 135)..μ,
          (1 / 2) * Real.log (min x ((71 / 135 - x) / 2) / (16 / 135)) ^ 2 / x :=
    integral_add_adjacent_intervals hI1 hI2
  rw [← hsplit]
  have hleft : (∫ x in (16 / 135)..(71 / 405),
        (1 / 2) * Real.log (min x ((71 / 135 - x) / 2) / (16 / 135)) ^ 2 / x)
      = (1 / 2) * (∫ x in (16 / 135)..(71 / 405), Real.log (x / (16 / 135)) ^ 2 / x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (16 / 135 : ℝ) ≤ 71 / 405)] at hx
    have hxa : x ≤ 71 / 405 := hx.2
    dsimp only
    rw [min_cap_eq, if_pos hxa, mul_div_assoc]
  have hright : (∫ x in (71 / 405)..μ,
        (1 / 2) * Real.log (min x ((71 / 135 - x) / 2) / (16 / 135)) ^ 2 / x)
      = (1 / 2) * (∫ x in (71 / 405)..μ, Real.log ((135 / 32) * (71 / 135 - x)) ^ 2 / x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hμ1] at hx
    dsimp only
    by_cases hxa : x ≤ 71 / 405
    · have hxeq : x = 71 / 405 := le_antisymm hxa hx.1
      subst hxeq
      rw [min_cap_eq, if_pos (le_refl _)]
      have harg : (71 / 405 : ℝ) / (16 / 135) = (135 / 32) * (71 / 135 - 71 / 405) := by
        norm_num
      rw [harg, mul_div_assoc]
    · rw [min_cap_eq, if_neg hxa, cap_log_eq, mul_div_assoc]
  rw [hleft, hright]


/-- `log (x/(16/135)) = log (0 + (135/16) x)`: the `Numeric565` linear integrand on `[a, 71/405]`. -/
private theorem integral_log_sq_first :
    (∫ x in (16 / 135)..(71 / 405), Real.log (x / (16 / 135)) ^ 2 / x)
      = ∫ t in (16 / 135)..(71 / 405), (Real.log (0 + (135 / 16) * t)) ^ 2 / t := by
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  have hx' : x / (16 / 135) = 0 + (135 / 16) * x := by
    field_simp
    ring
  rw [hx']

/-- The `Numeric565` linear integrand on the tail `[71/405, b]`. -/
private theorem integral_log_sq_lin :
    (∫ x in (71 / 405)..(89 / 462 - 0.00000001), Real.log (x / (16 / 135)) ^ 2 / x)
      = ∫ t in (71 / 405)..(89 / 462 - 0.00000001), (Real.log (0 + (135 / 16) * t)) ^ 2 / t := by
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  have hx' : x / (16 / 135) = 0 + (135 / 16) * x := by
    field_simp
    ring
  rw [hx']

/-- The capped integrand `log ((135/32)(71/135-x))` is the `Numeric565` `tripleTwo` integrand. -/
private theorem integral_log_sq_cap :
    (∫ x in (71 / 405)..(89 / 462 - 0.00000001), Real.log ((135 / 32) * (71 / 135 - x)) ^ 2 / x)
      = ∫ t in (71 / 405)..(89 / 462 - 0.00000001),
          (Real.log (71 / 32 + (-135 / 32) * t)) ^ 2 / t := by
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  have hx' : (135 / 32) * (71 / 135 - x) = 71 / 32 + (-135 / 32) * x := by
    ring
  rw [hx']

/-- The region `p q² ≤ Y^(71/135)` contributes exactly the two printed constants:
the capped double integral at weight `0.5617 (135/16)` equals
`(0.5617*135/32)(∫_a^(71/405) log(135t/16)^2/t + ∫_(71/405)^b log(71/32-135t/32)^2/t)`,
i.e. `tripleOne + tripleTwo` with the `Numeric565` definitions unfolded. -/
private theorem triple_band_eq_one_two :
    (0.5617 * (135 / 16)) *
        (∫ x in (16 / 135)..(89 / 462 - 0.00000001),
          (1 / 2) * Real.log (min x ((71 / 135 - x) / 2) / (16 / 135)) ^ 2 / x)
      = (0.5617 * (135 / 32)) *
          (∫ t in (16 / 135)..(71 / 405), (Real.log (0 + (135 / 16) * t)) ^ 2 / t)
        + (0.5617 * (135 / 32)) *
          (∫ t in (71 / 405)..(89 / 462 - 0.00000001),
            (Real.log (71 / 32 + (-135 / 32) * t)) ^ 2 / t) := by
  rw [triple_band_integral (μ := 89 / 462 - 0.00000001) (by norm_num) le_rfl,
    integral_log_sq_first, integral_log_sq_cap]
  ring


/-- The region `p q² > Y^(71/135)`: the complementary double integral is the difference of the two
squared-log integrals, i.e. exactly the `tripleThree` piece. -/
private theorem triple_band_eq_three :
    (0.5644 * (135 / 16)) *
        ((1 / 2) * (∫ x in (71 / 405)..(89 / 462 - 0.00000001),
            Real.log (x / (16 / 135)) ^ 2 / x)
          - (1 / 2) * (∫ x in (71 / 405)..(89 / 462 - 0.00000001),
            Real.log ((135 / 32) * (71 / 135 - x)) ^ 2 / x))
      = (0.5644 * (135 / 32)) *
          ((∫ t in (71 / 405)..(89 / 462 - 0.00000001), (Real.log (0 + (135 / 16) * t)) ^ 2 / t)
            - (∫ t in (71 / 405)..(89 / 462 - 0.00000001),
                (Real.log (71 / 32 + (-135 / 32) * t)) ^ 2 / t)) := by
  rw [integral_log_sq_lin, integral_log_sq_cap]
  ring


-- === tiling of a prime window by consecutive integer blocks ===
/-- A monotone chain of natural endpoints stays above its first point. -/
private theorem monotone_chain (n : ℕ → ℕ) :
    ∀ m : ℕ, (∀ i, i < m → n i ≤ n (i + 1)) → n 0 ≤ n m := by
  intro m
  induction m with
  | zero => intro _; exact le_rfl
  | succ m ih =>
    intro h
    exact le_trans (ih (fun i hi => h i (Nat.lt_succ_of_lt hi))) (h m (Nat.lt_succ_self m))

/-- A prime window splits without loss or duplication into consecutive blocks. -/
private theorem prime_sum_telescope {f : ℕ → ℝ} (n : ℕ → ℕ) :
    ∀ m : ℕ, (∀ i, i < m → n i ≤ n (i + 1)) →
      (∑ p ∈ (Ioc (n 0) (n m)).filter Nat.Prime, f p)
        = ∑ i ∈ Finset.range m, ∑ p ∈ (Ioc (n i) (n (i + 1))).filter Nat.Prime, f p := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hmono
    have hmm : n m ≤ n (m + 1) := hmono m (Nat.lt_succ_self m)
    have h0m : n 0 ≤ n m := monotone_chain n m (fun i hi => hmono i (Nat.lt_succ_of_lt hi))
    have hunion : Ioc (n 0) (n (m + 1)) = Ioc (n 0) (n m) ∪ Ioc (n m) (n (m + 1)) :=
      (Finset.Ioc_union_Ioc_eq_Ioc h0m hmm).symm
    have hdisj : Disjoint (Ioc (n 0) (n m)) (Ioc (n m) (n (m + 1))) := by
      apply Finset.disjoint_left.mpr
      intro x hx hx'
      rw [Finset.mem_Ioc] at hx hx'
      exact absurd hx'.1 (not_lt.mpr hx.2)
    have hdisj' : Disjoint ((Ioc (n 0) (n m)).filter Nat.Prime)
        ((Ioc (n m) (n (m + 1))).filter Nat.Prime) :=
      hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [hunion, Finset.filter_union, Finset.sum_union hdisj', sum_range_succ]
    rw [ih (fun i hi => hmono i (Nat.lt_succ_of_lt hi))]


-- === per-block reciprocal mass ===
/-- One block of the prime window has reciprocal mass at most its logarithmic length plus the
uniform Mertens error. The block uses `⌊Y^u⌋₊` as its lower endpoint while the deviation estimate
uses `⌈Y^u⌉₊`; the single integer between them costs `1/⌈Y^u⌉₊ ≤ 1/(a log Y)`. -/
private theorem block_prime_mass_le {Y u v : ℝ} (hY : 1 < Y)
    (hu1 : 16 / 135 ≤ u) (huv : u ≤ v) (hv2 : v ≤ 89 / 462 - 0.00000001)
    (hbig : 2 * Real.log 2 ≤ (16 / 135) * Real.log Y)
    (hne : ⌈Y ^ u⌉₊ ≤ ⌊Y ^ v⌋₊) :
    (∑ p ∈ (Ioc ⌊Y ^ u⌋₊ ⌊Y ^ v⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
      ≤ Real.log (v / u) + 42 * Real.log 2 / ((16 / 135) * Real.log Y) := by
  have hY0 : 0 < Y := by linarith
  have ha : (0 : ℝ) < 16 / 135 := by norm_num
  have hu0 : 0 < u := lt_of_lt_of_le ha hu1
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have haY : (0 : ℝ) < (16 / 135) * Real.log Y := by positivity
  have huY : (0 : ℝ) < u * Real.log Y := by positivity
  have hdev := prime_window_deviation (Y := Y) (x1 := u) (x2 := v) hY hu0 huv hu1 hv2
    (le_trans hbig (by nlinarith [hu1, hlogY])) hne
  obtain ⟨hlo, hhi⟩ := abs_le.mp hdev
  -- deviation window bound
  have hupper : (∑ p ∈ (Ioc ⌈Y ^ u⌉₊ ⌊Y ^ v⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
      ≤ Real.log (v / u) + 40 * Real.log 2 / ((16 / 135) * Real.log Y) := by
    have h1 : 40 * Real.log 2 / (u * Real.log Y) ≤ 40 * Real.log 2 / ((16 / 135) * Real.log Y) :=
      div_le_div_of_nonneg_left (by positivity) haY (by nlinarith [hu1, hlogY])
    linarith [hhi, h1]
  -- containment of the block in the deviation window together with one integer
  have hceil : ⌈Y ^ u⌉₊ ≤ ⌊Y ^ u⌋₊ + 1 := by
    have h1 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ Y ^ u by positivity)
    have h2 := Nat.lt_floor_add_one (Y ^ u)
    have h3 : ((⌈Y ^ u⌉₊ : ℕ) : ℝ) < ((⌊Y ^ u⌋₊ + 2 : ℕ) : ℝ) := by
      push_cast
      linarith
    have h4 : ⌈Y ^ u⌉₊ < ⌊Y ^ u⌋₊ + 2 := by exact_mod_cast h3
    omega
  have hsub : (Ioc ⌊Y ^ u⌋₊ ⌊Y ^ v⌋₊).filter Nat.Prime ⊆
      insert ⌈Y ^ u⌉₊ ((Ioc ⌈Y ^ u⌉₊ ⌊Y ^ v⌋₊).filter Nat.Prime) := by
    intro p hp
    obtain ⟨hpmem, hpp⟩ := Finset.mem_filter.mp hp
    rw [Finset.mem_Ioc] at hpmem
    by_cases h : ⌈Y ^ u⌉₊ < p
    · exact Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨h, hpmem.2⟩, hpp⟩)
    · push_neg at h
      have hstep : ⌈Y ^ u⌉₊ ≤ p := by omega
      have hpeq : p = ⌈Y ^ u⌉₊ := le_antisymm h hstep
      rw [hpeq]
      exact Finset.mem_insert_self _ _
  have hstep1 : (∑ p ∈ (Ioc ⌊Y ^ u⌋₊ ⌊Y ^ v⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
      ≤ ∑ p ∈ insert ⌈Y ^ u⌉₊ ((Ioc ⌈Y ^ u⌉₊ ⌊Y ^ v⌋₊).filter Nat.Prime),
          (1 : ℝ) / (p : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => by positivity)
  have hnotin : ⌈Y ^ u⌉₊ ∉ (Ioc ⌈Y ^ u⌉₊ ⌊Y ^ v⌋₊).filter Nat.Prime := by
    intro h
    have := (Finset.mem_filter.mp h).1
    rw [Finset.mem_Ioc] at this
    exact absurd this.1 (lt_irrefl _)
  have hstep2 : (∑ p ∈ insert ⌈Y ^ u⌉₊ ((Ioc ⌈Y ^ u⌉₊ ⌊Y ^ v⌋₊).filter Nat.Prime),
        (1 : ℝ) / (p : ℝ))
      = 1 / ((⌈Y ^ u⌉₊ : ℕ) : ℝ)
        + ∑ p ∈ (Ioc ⌈Y ^ u⌉₊ ⌊Y ^ v⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
    rw [Finset.sum_insert hnotin]
  -- the single integer costs at most `1/(a log Y)`
  have hone : 1 / ((⌈Y ^ u⌉₊ : ℕ) : ℝ) ≤ 1 / ((16 / 135) * Real.log Y) := by
    have hceilpos : (0 : ℝ) < ((⌈Y ^ u⌉₊ : ℕ) : ℝ) := by
      have := Nat.le_ceil (Y ^ u)
      have : (0 : ℝ) < Y ^ u := Real.rpow_pos_of_pos hY0 u
      linarith
    have hge : Y ^ u ≤ ((⌈Y ^ u⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h1 : 1 / ((⌈Y ^ u⌉₊ : ℕ) : ℝ) ≤ 1 / Y ^ u :=
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos hY0 u) hge
    have hexp : (u * Real.log Y) ≤ Y ^ u := by
      rw [Real.rpow_def_of_pos hY0 u]
      linarith [Real.add_one_le_exp (Real.log Y * u)]
    have h2 : 1 / Y ^ u ≤ 1 / (u * Real.log Y) :=
      one_div_le_one_div_of_le huY hexp
    have h3 : 1 / (u * Real.log Y) ≤ 1 / ((16 / 135) * Real.log Y) :=
      one_div_le_one_div_of_le haY (by nlinarith [hu1, hlogY])
    linarith
  have hl2half : (1 / 2 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hcomb : 40 * Real.log 2 / ((16 / 135) * Real.log Y) + 1 / ((16 / 135) * Real.log Y)
      ≤ 42 * Real.log 2 / ((16 / 135) * Real.log Y) := by
    rw [← add_div, div_le_div_iff_of_pos_right haY]
    nlinarith [hl2half]
  linarith [hstep1, hstep2, hupper, hone, hcomb]


-- === the block comparison ===
/-- A monotone weight against `dx/x`: the reciprocal prime sum over `(Y^a, Y^μ]` is at most the
integral plus a `K`-block staircase error and a Mertens error, `K` blocks of equal logarithmic mesh. -/
private theorem prime_sum_block_le
    {Y : ℝ} (hY : 1 < Y) {K : ℕ} (hK : 0 < K) {μ : ℝ}
    (hμ1 : 16 / 135 ≤ μ) (hμ2 : μ ≤ 89 / 462 - 0.00000001)
    (hbig : 2 * Real.log 2 ≤ (16 / 135) * Real.log Y)
    (φ : ℝ → ℝ)
    (hmono : ∀ x y : ℝ, 16 / 135 ≤ x → x ≤ y → y ≤ μ → φ x ≤ φ y)
    (hφnn : ∀ x : ℝ, 16 / 135 ≤ x → x ≤ μ → 0 ≤ φ x)
    (hint : ∀ u v : ℝ, 16 / 135 ≤ u → u ≤ v → v ≤ μ →
      IntervalIntegrable (fun x : ℝ => φ x / x) MeasureTheory.volume u v)
    (hne : ∀ i : ℕ, i < K →
      ⌈Y ^ (16 / 135 + (i : ℝ) * ((μ - 16 / 135) / (K : ℝ)))⌉₊
        ≤ ⌊Y ^ (16 / 135 + ((i : ℝ) + 1) * ((μ - 16 / 135) / (K : ℝ)))⌋₊) :
    (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ μ⌋₊).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ) * φ (Real.log (p : ℝ) / Real.log Y))
      ≤ (∫ x in (16 / 135)..μ, φ x / x)
        + φ μ * ((μ - 16 / 135) / ((16 / 135) * (K : ℝ))
            + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y))) := by
  have hY0 : 0 < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have ha : (0 : ℝ) < 16 / 135 := by norm_num
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  set w : ℝ := (μ - 16 / 135) / (K : ℝ) with hw
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  set c : ℕ → ℝ := fun i => 16 / 135 + (i : ℝ) * w with hc
  have hc0 : c 0 = 16 / 135 := by simp [hc]
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKpos
  have hcK : c K = μ := by
    rw [hc, hw]
    push_cast
    field_simp
    ring
  have hcmono : ∀ i : ℕ, c i ≤ c (i + 1) := by
    intro i
    rw [hc]
    push_cast
    nlinarith [hw0]
  have hci_ge : ∀ i : ℕ, 16 / 135 ≤ c i := by
    intro i
    rw [hc]
    have h0 : (0 : ℝ) ≤ (i : ℝ) * w := by positivity
    linarith
  have hci_mono_le : ∀ i : ℕ, i ≤ K → c i ≤ μ := by
    intro i hi
    calc c i = c K + (c i - c K) := by ring
      _ ≤ c K := by
          rw [hc]
          push_cast
          have h1 : (i : ℝ) * w ≤ (K : ℝ) * w := by
            apply mul_le_mul_of_nonneg_right _ hw0
            exact_mod_cast hi
          linarith
      _ = μ := hcK
  set n : ℕ → ℕ := fun i => ⌊Y ^ c i⌋₊ with hn
  have hnmono : ∀ i, i < K → n i ≤ n (i + 1) := by
    intro i _
    rw [hn]
    exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hY.le (hcmono i))
  -- the block bounds
  have hblock : ∀ i, i < K →
      (∑ p ∈ (Ioc (n i) (n (i + 1))).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ) * φ (Real.log (p : ℝ) / Real.log Y))
        ≤ (Real.log (c (i + 1) / c i) + 42 * Real.log 2 / ((16 / 135) * Real.log Y))
            * φ (c (i + 1)) := by
    intro i hi
    have hci : 16 / 135 ≤ c i := hci_ge i
    have hci1le : c (i + 1) ≤ μ := hci_mono_le (i + 1) hi
    have hci1nn : (0 : ℝ) ≤ φ (c (i + 1)) := hφnn _ (le_trans hci (hcmono i)) hci1le
    have hne' : ⌈Y ^ c i⌉₊ ≤ ⌊Y ^ c (i + 1)⌋₊ := by
      rw [hc, hw]
      push_cast
      exact hne i hi
    have hmass := block_prime_mass_le (Y := Y) (u := c i) (v := c (i + 1)) hY hci
      (hcmono i) (le_trans hci1le hμ2)
      (le_trans hbig (by nlinarith [hci, hlogY])) hne'
    have hpt : ∀ p ∈ (Ioc (n i) (n (i + 1))).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ) * φ (Real.log (p : ℝ) / Real.log Y)
          ≤ (1 : ℝ) / (p : ℝ) * φ (c (i + 1)) := by
      intro p hp
      obtain ⟨hpmem, hpp⟩ := Finset.mem_filter.mp hp
      rw [Finset.mem_Ioc] at hpmem
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have hlow : c i < Real.log (p : ℝ) / Real.log Y := by
        have h1 : Y ^ c i < (p : ℝ) := by
          have h2 := Nat.lt_floor_add_one (Y ^ c i)
          have h5 : ⌊Y ^ c i⌋₊ < p := by simpa only [hn] using hpmem.1
          have h3 : ((⌊Y ^ c i⌋₊ : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by
            exact_mod_cast Nat.succ_le_of_lt h5
          linarith
        have h4 := Real.log_lt_log (Real.rpow_pos_of_pos hY0 (c i)) h1
        rw [Real.log_rpow hY0] at h4
        rw [lt_div_iff₀ hlogY]
        linarith
      have hp2 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
      have hhigh : Real.log (p : ℝ) / Real.log Y ≤ c (i + 1) := by
        have h1 : (p : ℝ) ≤ Y ^ c (i + 1) := by
          have h2 : p ≤ n (i + 1) := hpmem.2
          have h3 : ((n (i + 1) : ℕ) : ℝ) ≤ Y ^ c (i + 1) := by
            rw [hn]
            exact Nat.floor_le (by positivity)
          exact le_trans (by exact_mod_cast h2) h3
        have h4 := Real.log_le_log (by linarith) h1
        rw [Real.log_rpow hY0] at h4
        rw [div_le_iff₀ hlogY]
        linarith
      have hbase : 16 / 135 ≤ Real.log (p : ℝ) / Real.log Y := le_trans hci hlow.le
      have hstep := hmono _ _ hbase hhigh hci1le
      exact mul_le_mul_of_nonneg_left hstep (by positivity)
    calc (∑ p ∈ (Ioc (n i) (n (i + 1))).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ) * φ (Real.log (p : ℝ) / Real.log Y))
        ≤ ∑ p ∈ (Ioc (n i) (n (i + 1))).filter Nat.Prime,
            (1 : ℝ) / (p : ℝ) * φ (c (i + 1)) := Finset.sum_le_sum hpt
      _ = (∑ p ∈ (Ioc (n i) (n (i + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
            * φ (c (i + 1)) := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hmass hci1nn
  -- the block integrals dominate the staircase coefficients
  have hInt : ∀ i, i < K →
      φ (c i) * Real.log (c (i + 1) / c i) ≤ ∫ x in (c i)..(c (i + 1)), φ x / x := by
    intro i hi
    have hci : 16 / 135 ≤ c i := hci_ge i
    have hci0 : (0 : ℝ) < c i := lt_of_lt_of_le ha hci
    have hci1le : c (i + 1) ≤ μ := hci_mono_le (i + 1) hi
    have hle := hcmono i
    have h1 : (∫ x in (c i)..(c (i + 1)), φ (c i) / x) ≤ ∫ x in (c i)..(c (i + 1)), φ x / x := by
      apply integral_mono_on (f := fun x : ℝ => φ (c i) / x) (g := fun x : ℝ => φ x / x)
        hle
      · apply ContinuousOn.intervalIntegrable_of_Icc hle
        apply ContinuousOn.div continuousOn_const continuousOn_id
        intro x hx
        exact ne_of_gt (lt_of_lt_of_le hci0 hx.1)
      · exact hint (c i) (c (i + 1)) hci hle hci1le
      · intro x hx
        have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hci0 hx.1
        have hstep : φ (c i) ≤ φ x := hmono _ _ hci hx.1 (le_trans hx.2 hci1le)
        exact div_le_div_of_nonneg_right hstep hx0.le
    have hci1pos : (0 : ℝ) < c (i + 1) := lt_of_lt_of_le hci0 (hcmono i)
    have h2 : (∫ x in (c i)..(c (i + 1)), φ (c i) / x)
        = φ (c i) * Real.log (c (i + 1) / c i) := by
      have hA : (∫ x in (c i)..(c (i + 1)), φ (c i) / x)
          = φ (c i) * ∫ x in (c i)..(c (i + 1)), 1 / x := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x _
        simp only [div_eq_mul_inv, one_mul]
      rw [hA, integral_one_div_of_pos hci0 hci1pos]
    rw [← h2]
    exact h1
  have hItel : (∑ i ∈ Finset.range K, ∫ x in (c i)..(c (i + 1)), φ x / x)
      = ∫ x in (c 0)..(c K), φ x / x := by
    have := intervalIntegral.sum_integral_adjacent_intervals
      (f := fun x : ℝ => φ x / x) (a := c) (n := K)
      (fun k hk => hint (c k) (c (k + 1)) (by
        rw [hc]
        have : (0 : ℝ) ≤ (k : ℝ) * w := by positivity
        linarith) (hcmono k) (by
        have hik : ((k : ℝ) + 1) ≤ (K : ℝ) := by
          have : k + 1 ≤ K := hk
          exact_mod_cast this
        calc c (k + 1) = c K + (c (k + 1) - c K) := by ring
          _ ≤ c K := by
              rw [hc]
              push_cast
              have h1 : ((k : ℝ) + 1) * w ≤ (K : ℝ) * w :=
                mul_le_mul_of_nonneg_right hik hw0
              linarith
          _ = μ := hcK))
    simpa using this
  -- the staircase coefficient error
  have hlogratio : ∀ i, i < K → Real.log (c (i + 1) / c i) ≤ w / (16 / 135) := by
    intro i hi
    have hci : 16 / 135 ≤ c i := hci_ge i
    have hci0 : (0 : ℝ) < c i := lt_of_lt_of_le ha hci
    have hstep : c (i + 1) / c i = 1 + w / c i := by
      rw [hc]
      push_cast
      field_simp
      ring
    rw [hstep]
    have hpos : (0 : ℝ) ≤ w / c i := by positivity
    calc Real.log (1 + w / c i) ≤ 1 + w / c i - 1 := Real.log_le_sub_one_of_pos (by linarith)
      _ = w / c i := by ring
      _ ≤ w / (16 / 135) := by
          apply div_le_div_of_nonneg_left hw0 ha hci
  have hdiff : ∀ i, i < K → (0 : ℝ) ≤ φ (c (i + 1)) - φ (c i) := by
    intro i hi
    have hci : 16 / 135 ≤ c i := hci_ge i
    have hci1le : c (i + 1) ≤ μ := hci_mono_le (i + 1) hi
    have := hmono _ _ hci (hcmono i) hci1le
    linarith
  have htele2 : (∑ i ∈ Finset.range K, (φ (c (i + 1)) - φ (c i))) = φ (c K) - φ (c 0) := by
    rw [← Nat.Ico_zero_eq_range]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (sum_Ico_sub (fun i : ℕ => φ (c i)) (Nat.zero_le K))
  have hphi0 : (0 : ℝ) ≤ φ (16 / 135) := hφnn _ le_rfl hμ1
  have hphimono : φ (c K) ≤ φ μ := by
    rw [hcK]
  -- assemble
  have hsumle : (∑ i ∈ Finset.range K,
        (∑ p ∈ (Ioc (n i) (n (i + 1))).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ) * φ (Real.log (p : ℝ) / Real.log Y)))
      ≤ ∑ i ∈ Finset.range K,
          (Real.log (c (i + 1) / c i) + 42 * Real.log 2 / ((16 / 135) * Real.log Y))
            * φ (c (i + 1)) :=
    Finset.sum_le_sum (fun i hi => hblock i (Finset.mem_range.mp hi))
  -- termwise: log-ratio times the upper value is the block integral plus a variation term
  have hterm : ∀ i, i < K →
      (Real.log (c (i + 1) / c i) + 42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ (c (i + 1))
        ≤ (∫ x in (c i)..(c (i + 1)), φ x / x)
          + (w / (16 / 135)) * (φ (c (i + 1)) - φ (c i))
          + (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ μ := by
    intro i hi
    have hLi := hlogratio i hi
    have hIi := hInt i hi
    have hdi := hdiff i hi
    have hnn : (0 : ℝ) ≤ φ (c (i + 1)) := hφnn _ (hci_ge (i + 1)) (hci_mono_le (i + 1) hi)
    have hstep1 : Real.log (c (i + 1) / c i) * φ (c (i + 1))
        = Real.log (c (i + 1) / c i) * φ (c i)
          + Real.log (c (i + 1) / c i) * (φ (c (i + 1)) - φ (c i)) := by ring
    have hstep2 : Real.log (c (i + 1) / c i) * φ (c i) ≤ ∫ x in (c i)..(c (i + 1)), φ x / x := by
      rw [mul_comm]
      exact hIi
    have hstep3 : Real.log (c (i + 1) / c i) * (φ (c (i + 1)) - φ (c i))
        ≤ (w / (16 / 135)) * (φ (c (i + 1)) - φ (c i)) :=
      mul_le_mul_of_nonneg_right hLi hdi
    have hphii : φ (c (i + 1)) ≤ φ μ :=
      hmono _ _ (hci_ge (i + 1)) (hci_mono_le (i + 1) hi) le_rfl
    have hstep4 : (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ (c (i + 1))
        ≤ (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ μ :=
      mul_le_mul_of_nonneg_left hphii (by positivity)
    nlinarith [hstep1, hstep2, hstep3, hstep4]
  have hmain : (∑ i ∈ Finset.range K,
          (Real.log (c (i + 1) / c i) + 42 * Real.log 2 / ((16 / 135) * Real.log Y))
            * φ (c (i + 1)))
      ≤ (∫ x in (16 / 135)..μ, φ x / x)
        + (w / (16 / 135)) * φ μ
        + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ μ := by
    have h1 : (∑ i ∈ Finset.range K,
          (Real.log (c (i + 1) / c i) + 42 * Real.log 2 / ((16 / 135) * Real.log Y))
            * φ (c (i + 1)))
        ≤ ∑ i ∈ Finset.range K, ((∫ x in (c i)..(c (i + 1)), φ x / x)
          + (w / (16 / 135)) * (φ (c (i + 1)) - φ (c i))
          + (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ μ) :=
      Finset.sum_le_sum (fun i hi => hterm i (Finset.mem_range.mp hi))
    have h2 : (∑ i ∈ Finset.range K, ((∫ x in (c i)..(c (i + 1)), φ x / x)
          + (w / (16 / 135)) * (φ (c (i + 1)) - φ (c i))
          + (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ μ))
        = (∑ i ∈ Finset.range K, ∫ x in (c i)..(c (i + 1)), φ x / x)
          + (w / (16 / 135)) * (∑ i ∈ Finset.range K, (φ (c (i + 1)) - φ (c i)))
          + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ μ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    have hI : (∑ i ∈ Finset.range K, ∫ x in (c i)..(c (i + 1)), φ x / x)
        = ∫ x in (16 / 135)..μ, φ x / x := by
      rw [hItel, hc0, hcK]
    have hD : (∑ i ∈ Finset.range K, (φ (c (i + 1)) - φ (c i))) ≤ φ μ := by
      rw [htele2, hc0, hcK]
      linarith [hphi0]
    have hDnn : (0 : ℝ) ≤ w / (16 / 135) := by positivity
    have hm := mul_le_mul_of_nonneg_left hD hDnn
    calc (∑ i ∈ Finset.range K,
          (Real.log (c (i + 1) / c i) + 42 * Real.log 2 / ((16 / 135) * Real.log Y))
            * φ (c (i + 1)))
        ≤ ∑ i ∈ Finset.range K, ((∫ x in (c i)..(c (i + 1)), φ x / x)
          + (w / (16 / 135)) * (φ (c (i + 1)) - φ (c i))
          + (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ μ) := h1
      _ = (∑ i ∈ Finset.range K, ∫ x in (c i)..(c (i + 1)), φ x / x)
          + (w / (16 / 135)) * (∑ i ∈ Finset.range K, (φ (c (i + 1)) - φ (c i)))
          + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ μ := h2
      _ ≤ (∫ x in (16 / 135)..μ, φ x / x)
          + (w / (16 / 135)) * φ μ
          + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ μ := by
          linarith [hI, hm]
  -- convert the staircase bound to the goal's normalisation
  have hw' : w / (16 / 135) = (μ - 16 / 135) / ((16 / 135) * (K : ℝ)) := by
    rw [hw]
    field_simp
    try ring
  have hgoal : (∑ i ∈ Finset.range K,
        (Real.log (c (i + 1) / c i) + 42 * Real.log 2 / ((16 / 135) * Real.log Y))
          * φ (c (i + 1)))
      ≤ (∫ x in (16 / 135)..μ, φ x / x)
        + φ μ * ((μ - 16 / 135) / ((16 / 135) * (K : ℝ))
            + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y))) := by
    have h1 := hmain
    rw [hw'] at h1
    nlinarith [h1]
  have htele := prime_sum_telescope
    (f := fun p => (1 : ℝ) / (p : ℝ) * φ (Real.log (p : ℝ) / Real.log Y)) n K hnmono
  have hn0' : n 0 = ⌊Y ^ (16 / 135 : ℝ)⌋₊ := by
    simp only [hn]
    exact congrArg (fun z : ℝ => ⌊Y ^ z⌋₊) hc0
  have hnK' : n K = ⌊Y ^ μ⌋₊ := by
    simp only [hn]
    exact congrArg (fun z : ℝ => ⌊Y ^ z⌋₊) hcK
  have htele' : (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ μ⌋₊).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ) * φ (Real.log (p : ℝ) / Real.log Y))
      = ∑ i ∈ Finset.range K, ∑ p ∈ (Ioc (n i) (n (i + 1))).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ) * φ (Real.log (p : ℝ) / Real.log Y) := by
    rw [← hn0', ← hnK']
    exact htele
  rw [htele']
  exact le_trans hsumle hgoal


-- === the inner level: the `log(y/a)` weight with a variable cut ===
/-- Instantiation of the block comparison at the source weight `log (y/a)`, i.e. the inner `r`-sum of
one fixed outer prime: at most `log (μ/a)²/2` plus the staircase and Mertens errors. -/
private theorem inner_q_sum_le {Y : ℝ} (hY : 1 < Y) {K : ℕ} (hK : 0 < K) {μ : ℝ}
    (hμ1 : 16 / 135 ≤ μ) (hμ2 : μ ≤ 89 / 462 - 0.00000001)
    (hbig : 2 * Real.log 2 ≤ (16 / 135) * Real.log Y)
    (hne : ∀ i : ℕ, i < K →
      ⌈Y ^ (16 / 135 + (i : ℝ) * ((μ - 16 / 135) / (K : ℝ)))⌉₊
        ≤ ⌊Y ^ (16 / 135 + ((i : ℝ) + 1) * ((μ - 16 / 135) / (K : ℝ)))⌋₊) :
    (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ μ⌋₊).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ) * Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)))
      ≤ (1 / 2) * Real.log (μ / (16 / 135)) ^ 2
        + Real.log (μ / (16 / 135))
            * ((μ - 16 / 135) / ((16 / 135) * (K : ℝ))
                + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y))) := by
  have hY0 : 0 < Y := by linarith
  have ha : (0 : ℝ) < 16 / 135 := by norm_num
  have hmain := prime_sum_block_le (Y := Y) (K := K) (μ := μ) hY hK hμ1 hμ2 hbig
    (fun y : ℝ => Real.log (y / (16 / 135)))
    (fun x y hx hxy hy => by
      apply Real.log_le_log (by linarith)
      exact div_le_div_of_nonneg_right hxy (by norm_num))
    (fun x hx _ => Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith))
    (fun u v hu huv hv => by
      apply ContinuousOn.intervalIntegrable_of_Icc huv
      have hu0 : (0 : ℝ) < u := lt_of_lt_of_le ha hu
      have hne0 : ∀ x ∈ Set.Icc u v, x ≠ 0 := by
        intro x hx
        have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hu0 hx.1
        linarith
      have hpos : ∀ x ∈ Set.Icc u v, x / (16 / 135) ≠ 0 := by
        intro x hx
        have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hu0 hx.1
        exact div_ne_zero (ne_of_gt hx0) (by norm_num)
      exact (ContinuousOn.log (by fun_prop) hpos).div continuousOn_id hne0)
    hne
  have hint : (∫ x in (16 / 135)..μ, Real.log (x / (16 / 135)) / x)
      = Real.log (μ / (16 / 135)) ^ 2 / 2 :=
    Integral565.integral_log_ratio (16 / 135) μ ha hμ1
  rw [hint] at hmain
  linarith [hmain]


/-- The decreasing mirror of the block comparison: for an antitone nonnegative weight the staircase
error is bounded by the value at the left endpoint instead of the right one. -/
private theorem prime_sum_block_decreasing_le
    {Y : ℝ} (hY : 1 < Y) {K : ℕ} (hK : 0 < K) {μ : ℝ}
    (hμ1 : 16 / 135 ≤ μ) (hμ2 : μ ≤ 89 / 462 - 0.00000001)
    (hbig : 2 * Real.log 2 ≤ (16 / 135) * Real.log Y)
    (φ : ℝ → ℝ)
    (hanti : ∀ x y : ℝ, 16 / 135 ≤ x → x ≤ y → y ≤ μ → φ y ≤ φ x)
    (hφnn : ∀ x : ℝ, 16 / 135 ≤ x → x ≤ μ → 0 ≤ φ x)
    (hint : ∀ u v : ℝ, 16 / 135 ≤ u → u ≤ v → v ≤ μ →
      IntervalIntegrable (fun x : ℝ => φ x / x) MeasureTheory.volume u v)
    (hne : ∀ i : ℕ, i < K →
      ⌈Y ^ (16 / 135 + (i : ℝ) * ((μ - 16 / 135) / (K : ℝ)))⌉₊
        ≤ ⌊Y ^ (16 / 135 + ((i : ℝ) + 1) * ((μ - 16 / 135) / (K : ℝ)))⌋₊) :
    (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ μ⌋₊).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ) * φ (Real.log (p : ℝ) / Real.log Y))
      ≤ (∫ x in (16 / 135)..μ, φ x / x)
        + φ (16 / 135) * ((μ - 16 / 135) / ((16 / 135) * (K : ℝ))
            + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y))) := by
  have hY0 : 0 < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have ha : (0 : ℝ) < 16 / 135 := by norm_num
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  set w : ℝ := (μ - 16 / 135) / (K : ℝ) with hw
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  set c : ℕ → ℝ := fun i => 16 / 135 + (i : ℝ) * w with hc
  have hc0 : c 0 = 16 / 135 := by simp [hc]
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKpos
  have hcK : c K = μ := by
    rw [hc, hw]
    push_cast
    field_simp
    ring
  have hcmono : ∀ i : ℕ, c i ≤ c (i + 1) := by
    intro i
    rw [hc]
    push_cast
    nlinarith [hw0]
  have hci_ge : ∀ i : ℕ, 16 / 135 ≤ c i := by
    intro i
    rw [hc]
    have h0 : (0 : ℝ) ≤ (i : ℝ) * w := by positivity
    linarith
  have hci_mono_le : ∀ i : ℕ, i ≤ K → c i ≤ μ := by
    intro i hi
    calc c i = c K + (c i - c K) := by ring
      _ ≤ c K := by
          rw [hc]
          push_cast
          have h1 : (i : ℝ) * w ≤ (K : ℝ) * w := by
            apply mul_le_mul_of_nonneg_right _ hw0
            exact_mod_cast hi
          linarith
      _ = μ := hcK
  set n : ℕ → ℕ := fun i => ⌊Y ^ c i⌋₊ with hn
  have hnmono : ∀ i, i < K → n i ≤ n (i + 1) := by
    intro i _
    rw [hn]
    exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hY.le (hcmono i))
  -- block bounds, now against the left endpoint
  have hblock : ∀ i, i < K →
      (∑ p ∈ (Ioc (n i) (n (i + 1))).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ) * φ (Real.log (p : ℝ) / Real.log Y))
        ≤ (Real.log (c (i + 1) / c i) + 42 * Real.log 2 / ((16 / 135) * Real.log Y))
            * φ (c i) := by
    intro i hi
    have hci : 16 / 135 ≤ c i := hci_ge i
    have hci1le : c (i + 1) ≤ μ := hci_mono_le (i + 1) hi
    have hcin : (0 : ℝ) ≤ φ (c i) := hφnn _ hci (le_trans (hcmono i) hci1le)
    have hne' : ⌈Y ^ c i⌉₊ ≤ ⌊Y ^ c (i + 1)⌋₊ := by
      rw [hc, hw]
      push_cast
      exact hne i hi
    have hmass := block_prime_mass_le (Y := Y) (u := c i) (v := c (i + 1)) hY hci
      (hcmono i) (le_trans hci1le hμ2)
      (le_trans hbig (by nlinarith [hci, hlogY])) hne'
    have hpt : ∀ p ∈ (Ioc (n i) (n (i + 1))).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ) * φ (Real.log (p : ℝ) / Real.log Y)
          ≤ (1 : ℝ) / (p : ℝ) * φ (c i) := by
      intro p hp
      obtain ⟨hpmem, hpp⟩ := Finset.mem_filter.mp hp
      rw [Finset.mem_Ioc] at hpmem
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have hlow : c i < Real.log (p : ℝ) / Real.log Y := by
        have h1 : Y ^ c i < (p : ℝ) := by
          have h2 := Nat.lt_floor_add_one (Y ^ c i)
          have h5 : ⌊Y ^ c i⌋₊ < p := by simpa only [hn] using hpmem.1
          have h3 : ((⌊Y ^ c i⌋₊ : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by
            exact_mod_cast Nat.succ_le_of_lt h5
          linarith
        have h4 := Real.log_lt_log (Real.rpow_pos_of_pos hY0 (c i)) h1
        rw [Real.log_rpow hY0] at h4
        rw [lt_div_iff₀ hlogY]
        linarith
      have hp2 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
      have hhigh : Real.log (p : ℝ) / Real.log Y ≤ c (i + 1) := by
        have h1 : (p : ℝ) ≤ Y ^ c (i + 1) := by
          have h2 : p ≤ n (i + 1) := hpmem.2
          have h3 : ((n (i + 1) : ℕ) : ℝ) ≤ Y ^ c (i + 1) := by
            rw [hn]
            exact Nat.floor_le (by positivity)
          exact le_trans (by exact_mod_cast h2) h3
        have h4 := Real.log_le_log (by linarith) h1
        rw [Real.log_rpow hY0] at h4
        rw [div_le_iff₀ hlogY]
        linarith
      have hstep := hanti _ _ hci hlow.le (le_trans hhigh hci1le)
      exact mul_le_mul_of_nonneg_left hstep (by positivity)
    calc (∑ p ∈ (Ioc (n i) (n (i + 1))).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ) * φ (Real.log (p : ℝ) / Real.log Y))
        ≤ ∑ p ∈ (Ioc (n i) (n (i + 1))).filter Nat.Prime,
            (1 : ℝ) / (p : ℝ) * φ (c i) := Finset.sum_le_sum hpt
      _ = (∑ p ∈ (Ioc (n i) (n (i + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
            * φ (c i) := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hmass hcin
  -- the block integral dominates the *right* endpoint value
  have hInt : ∀ i, i < K →
      φ (c (i + 1)) * Real.log (c (i + 1) / c i) ≤ ∫ x in (c i)..(c (i + 1)), φ x / x := by
    intro i hi
    have hci : 16 / 135 ≤ c i := hci_ge i
    have hci0 : (0 : ℝ) < c i := lt_of_lt_of_le ha hci
    have hci1le : c (i + 1) ≤ μ := hci_mono_le (i + 1) hi
    have hle := hcmono i
    have h1 : (∫ x in (c i)..(c (i + 1)), φ (c (i + 1)) / x) ≤ ∫ x in (c i)..(c (i + 1)), φ x / x := by
      apply integral_mono_on (f := fun x : ℝ => φ (c (i + 1)) / x) (g := fun x : ℝ => φ x / x) hle
      · apply ContinuousOn.intervalIntegrable_of_Icc hle
        apply ContinuousOn.div continuousOn_const continuousOn_id
        intro x hx
        exact ne_of_gt (lt_of_lt_of_le hci0 hx.1)
      · exact hint (c i) (c (i + 1)) hci hle hci1le
      · intro x hx
        have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hci0 hx.1
        have hbase : 16 / 135 ≤ x := le_trans hci hx.1
        have hstep : φ (c (i + 1)) ≤ φ x := hanti x (c (i + 1)) hbase hx.2 hci1le
        exact div_le_div_of_nonneg_right hstep hx0.le
    have hci1pos : (0 : ℝ) < c (i + 1) := lt_of_lt_of_le hci0 hle
    have h2 : (∫ x in (c i)..(c (i + 1)), φ (c (i + 1)) / x)
        = φ (c (i + 1)) * Real.log (c (i + 1) / c i) := by
      have hA : (∫ x in (c i)..(c (i + 1)), φ (c (i + 1)) / x)
          = φ (c (i + 1)) * ∫ x in (c i)..(c (i + 1)), 1 / x := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x _
        simp only [div_eq_mul_inv, one_mul]
      rw [hA, integral_one_div_of_pos hci0 hci1pos]
    rw [← h2]
    exact h1
  have hItel : (∑ i ∈ Finset.range K, ∫ x in (c i)..(c (i + 1)), φ x / x)
      = ∫ x in (c 0)..(c K), φ x / x := by
    have := intervalIntegral.sum_integral_adjacent_intervals
      (f := fun x : ℝ => φ x / x) (a := c) (n := K)
      (fun k hk => hint (c k) (c (k + 1)) (hci_ge k) (hcmono k) (hci_mono_le (k + 1) hk))
    simpa using this
  have hlogratio : ∀ i, i < K → Real.log (c (i + 1) / c i) ≤ w / (16 / 135) := by
    intro i hi
    have hci : 16 / 135 ≤ c i := hci_ge i
    have hci0 : (0 : ℝ) < c i := lt_of_lt_of_le ha hci
    have hstep : c (i + 1) / c i = 1 + w / c i := by
      rw [hc]
      push_cast
      field_simp
      ring
    rw [hstep]
    calc Real.log (1 + w / c i) ≤ 1 + w / c i - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ = w / c i := by ring
      _ ≤ w / (16 / 135) := div_le_div_of_nonneg_left hw0 ha hci
  have hdec : ∀ i, i < K → (0 : ℝ) ≤ φ (c i) - φ (c (i + 1)) := by
    intro i hi
    have hstep := hanti _ _ (hci_ge i) (hcmono i) (hci_mono_le (i + 1) hi)
    linarith
  have htele2 : (∑ i ∈ Finset.range K, (φ (c i) - φ (c (i + 1)))) = φ (c 0) - φ (c K) := by
    have h := sum_Ico_sub (fun i : ℕ => φ (c i)) (Nat.zero_le K)
    rw [← Nat.Ico_zero_eq_range]
    have hstep : (∑ i ∈ Finset.Ico 0 K, (φ (c i) - φ (c (i + 1))))
        = - ∑ i ∈ Finset.Ico 0 K, (φ (c (i + 1)) - φ (c i)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hstep, h]
    ring
  have hphi0 : (0 : ℝ) ≤ φ (16 / 135) := hφnn _ le_rfl hμ1
  -- assemble
  have hsumle : (∑ i ∈ Finset.range K,
        (∑ p ∈ (Ioc (n i) (n (i + 1))).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ) * φ (Real.log (p : ℝ) / Real.log Y)))
      ≤ ∑ i ∈ Finset.range K,
          (Real.log (c (i + 1) / c i) + 42 * Real.log 2 / ((16 / 135) * Real.log Y))
            * φ (c i) :=
    Finset.sum_le_sum (fun i hi => hblock i (Finset.mem_range.mp hi))
  have hterm : ∀ i, i < K →
      (Real.log (c (i + 1) / c i) + 42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ (c i)
        ≤ (∫ x in (c i)..(c (i + 1)), φ x / x)
          + (w / (16 / 135)) * (φ (c i) - φ (c (i + 1)))
          + (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ (16 / 135) := by
    intro i hi
    have hLi := hlogratio i hi
    have hIi := hInt i hi
    have hdi := hdec i hi
    have hphii : φ (c i) ≤ φ (16 / 135) :=
      hanti (16 / 135) (c i) le_rfl (hci_ge i) (hci_mono_le i (le_of_lt hi))
    have hnn : (0 : ℝ) ≤ φ (c i) := hφnn _ (hci_ge i) (le_trans (hci_mono_le i (le_of_lt hi)) le_rfl)
    have hstep1 : Real.log (c (i + 1) / c i) * φ (c i)
        = Real.log (c (i + 1) / c i) * φ (c (i + 1))
          + Real.log (c (i + 1) / c i) * (φ (c i) - φ (c (i + 1))) := by ring
    have hstep3 : Real.log (c (i + 1) / c i) * (φ (c i) - φ (c (i + 1)))
        ≤ (w / (16 / 135)) * (φ (c i) - φ (c (i + 1))) :=
      mul_le_mul_of_nonneg_right hLi hdi
    have hstep4 : (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ (c i)
        ≤ (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ (16 / 135) :=
      mul_le_mul_of_nonneg_left hphii (by positivity)
    nlinarith [hstep1, hstep3, hstep4, hIi]
  have hmain : (∑ i ∈ Finset.range K,
          (Real.log (c (i + 1) / c i) + 42 * Real.log 2 / ((16 / 135) * Real.log Y))
            * φ (c i))
      ≤ (∫ x in (16 / 135)..μ, φ x / x)
        + (w / (16 / 135)) * φ (16 / 135)
        + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ (16 / 135) := by
    have h1 : (∑ i ∈ Finset.range K,
          (Real.log (c (i + 1) / c i) + 42 * Real.log 2 / ((16 / 135) * Real.log Y))
            * φ (c i))
        ≤ ∑ i ∈ Finset.range K, ((∫ x in (c i)..(c (i + 1)), φ x / x)
          + (w / (16 / 135)) * (φ (c i) - φ (c (i + 1)))
          + (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ (16 / 135)) :=
      Finset.sum_le_sum (fun i hi => hterm i (Finset.mem_range.mp hi))
    have h2 : (∑ i ∈ Finset.range K, ((∫ x in (c i)..(c (i + 1)), φ x / x)
          + (w / (16 / 135)) * (φ (c i) - φ (c (i + 1)))
          + (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ (16 / 135)))
        = (∑ i ∈ Finset.range K, ∫ x in (c i)..(c (i + 1)), φ x / x)
          + (w / (16 / 135)) * (∑ i ∈ Finset.range K, (φ (c i) - φ (c (i + 1))))
          + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ (16 / 135) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    have hI : (∑ i ∈ Finset.range K, ∫ x in (c i)..(c (i + 1)), φ x / x)
        = ∫ x in (16 / 135)..μ, φ x / x := by
      rw [hItel, hc0, hcK]
    have hD : (∑ i ∈ Finset.range K, (φ (c i) - φ (c (i + 1)))) ≤ φ (16 / 135) := by
      rw [htele2, hc0, hcK]
      have hnn : (0 : ℝ) ≤ φ μ := hφnn μ hμ1 le_rfl
      linarith [hphi0]
    have hDnn : (0 : ℝ) ≤ w / (16 / 135) := by positivity
    have hm := mul_le_mul_of_nonneg_left hD hDnn
    calc (∑ i ∈ Finset.range K,
          (Real.log (c (i + 1) / c i) + 42 * Real.log 2 / ((16 / 135) * Real.log Y))
            * φ (c i))
        ≤ ∑ i ∈ Finset.range K, ((∫ x in (c i)..(c (i + 1)), φ x / x)
          + (w / (16 / 135)) * (φ (c i) - φ (c (i + 1)))
          + (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ (16 / 135)) := h1
      _ = (∑ i ∈ Finset.range K, ∫ x in (c i)..(c (i + 1)), φ x / x)
          + (w / (16 / 135)) * (∑ i ∈ Finset.range K, (φ (c i) - φ (c (i + 1))))
          + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ (16 / 135) := h2
      _ ≤ (∫ x in (16 / 135)..μ, φ x / x)
          + (w / (16 / 135)) * φ (16 / 135)
          + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ (16 / 135) := by
          linarith [hI, hm]
  have hw' : w / (16 / 135) = (μ - 16 / 135) / ((16 / 135) * (K : ℝ)) := by
    rw [hw]
    field_simp
    try ring
  have hgoal : (∑ i ∈ Finset.range K,
        (Real.log (c (i + 1) / c i) + 42 * Real.log 2 / ((16 / 135) * Real.log Y))
          * φ (c i))
      ≤ (∫ x in (16 / 135)..μ, φ x / x)
        + φ (16 / 135) * ((μ - 16 / 135) / ((16 / 135) * (K : ℝ))
            + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y))) := by
    have h1 := hmain
    rw [hw'] at h1
    nlinarith [h1]
  have htele := prime_sum_telescope
    (f := fun p => (1 : ℝ) / (p : ℝ) * φ (Real.log (p : ℝ) / Real.log Y)) n K hnmono
  have hn0' : n 0 = ⌊Y ^ (16 / 135 : ℝ)⌋₊ := by
    simp only [hn]
    exact congrArg (fun z : ℝ => ⌊Y ^ z⌋₊) hc0
  have hnK' : n K = ⌊Y ^ μ⌋₊ := by
    simp only [hn]
    exact congrArg (fun z : ℝ => ⌊Y ^ z⌋₊) hcK
  have htele' : (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ μ⌋₊).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ) * φ (Real.log (p : ℝ) / Real.log Y))
      = ∑ i ∈ Finset.range K, ∑ p ∈ (Ioc (n i) (n (i + 1))).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ) * φ (Real.log (p : ℝ) / Real.log Y) := by
    rw [← hn0', ← hnK']
    exact htele
  rw [htele']
  exact le_trans hsumle hgoal

-- =====================================================================
-- Bricks of pass `OMOS lomos 20261116T1759Z` (verified, `const_le` etc.).
-- =====================================================================

/-
WIP scratch for Languasco2004/Decomp578d, leaf `triple_prime_sum_upper`.
Not a lab file: nothing here is intended for commit as-is.
Keep: (i) the earlier kernel-checked record that the lossy Chebyshev route cannot close the
leaf, (ii) the bricks of the pass `OMOS lomos 20261116T1759Z` (see 578d-notes-20261116T1759Z.md).
-/

namespace LeanLab.Languasco2004.Decomp578d
open Real Finset intervalIntegral Decomp279a Decomp316a Source565 Sieve565 Numeric565 Reserve578
noncomputable section
open Decomp578c

/-- `log ((89/462)/(16/135)) ≥ 0.4857`, from the certified polynomial enclosure
`LogApprox565.logPoly_error` (error at most `1e-9`) already in this lane. -/
private theorem log_boundary_ge : (0.4857 : ℝ) ≤ Real.log ((89 : ℝ) / 462 / (16 / 135)) := by
  have heq : ((89 : ℝ) / 462 / (16 / 135)) = (12015 / 7392 : ℝ) := by norm_num
  rw [heq]
  have h := LeanLab.Languasco2004.LogApprox565.logPoly_error (12015 / 7392 : ℝ)
    (by norm_num) (by norm_num)
  have hb := (abs_le.mp h).1
  have hp : (0.4857 : ℝ) + 1 / 1000000 ≤
      LeanLab.Languasco2004.LogApprox565.logPoly (12015 / 7392 : ℝ) := by
    unfold LeanLab.Languasco2004.LogApprox565.logPoly
    norm_num [Finset.sum_range_succ]
  linarith

/-- The 1/6-symmetry + Mertens crude bound for the ordered triple reciprocal sum,
multiplied by the model's constant, is strictly larger than the target constant
`tripleOne + tripleTwo + tripleThree`. -/
private theorem crude_ordered_bound_insufficient :
    tripleOne + tripleTwo + tripleThree
      < (135 / 16) * 0.5644 * ((Real.log ((89 : ℝ) / 462 / (16 / 135))) ^ 3 / 6) := by
  have h1 := tripleOne_bound
  have h2 := tripleTwo_bound
  have h3 := tripleThree_bound
  have hL := log_boundary_ge
  have hcube : ((0.4857 : ℝ)) ^ 3 ≤ (Real.log ((89 : ℝ) / 462 / (16 / 135))) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) hL 3
  nlinarith


-- =====================================================================================
-- Bricks of pass `OMOS lomos 20261116T1759Z`.
--
-- The model triple sum has the leading term `(135/16) * [0.5617 * A + 0.5644 * B]`, with
-- `a = 16/135`, `K = 71/135`, `c = K/3 = 71/405`, `b = 89/462 - 1e-8` and
--   A = (1/2)∫_a^c (log (u/a))^2/u + (1/2)∫_c^b (log ((K-u)/(2a)))^2/u     (sharp branch),
--   B = (1/2)∫_c^b [(log (u/a))^2 - (log ((K-u)/(2a)))^2]/u                 (upper branch),
-- and the source constant dominates it by `2.9096e-8` (verified numerically).
-- =====================================================================================

/-- B1: `∫_a^b (log (u/a))^2/u = (log (b/a))^3/3`. -/
private theorem integral_logsq_ratio (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ u in a..b, log (u / a) ^ 2 / u) = log (b / a) ^ 3 / 3 := by
  have hd : ∀ u ∈ Set.uIcc a b,
      HasDerivAt (fun v : ℝ => log (v / a) ^ 3 / 3) (log (u / a) ^ 2 / u) u := by
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    have hu0 : 0 < u := ha.trans_le hu.1
    have h := (((hasDerivAt_id u).div_const a).log (div_ne_zero hu0.ne' ha.ne')).pow 3
    have h' := h.div_const 3
    simp only [Pi.pow_apply, id_eq] at h'
    convert h' using 1 <;> field_simp <;> ring
  have hi : IntervalIntegrable (fun u => log (u / a) ^ 2 / u) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    apply ContinuousOn.div
    · apply ContinuousOn.pow
      apply ContinuousOn.log
      · fun_prop
      · intro u hu
        exact div_ne_zero (ne_of_gt (ha.trans_le hu.1)) ha.ne'
    · fun_prop
    · intro u hu
      exact ne_of_gt (ha.trans_le hu.1)
  have h := integral_eq_sub_of_hasDerivAt hd hi
  simpa only [div_self ha.ne', log_one, zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_div,
    sub_zero] using h

/-- B2a: `tripleOne` is the elementary `(log (u/a))^2/u` integral over `[16/135, 71/405]`. -/
private theorem tripleOne_eq :
    tripleOne = (0.5617 * (135 / 32)) *
      (log ((71 / 405 : ℝ) / (16 / 135)) ^ 3 / 3) := by
  have harg : ∀ u : ℝ, (0 + (135 / 16) * u) = u / (16 / 135) := by
    intro u; field_simp; ring
  unfold tripleOne
  rw [show (∫ t in (16 / 135 : ℝ)..(71 / 405 : ℝ), log (0 + (135 / 16) * t) ^ 2 / t)
      = ∫ t in (16 / 135 : ℝ)..(71 / 405 : ℝ), log (t / (16 / 135)) ^ 2 / t from by
    apply integral_congr
    intro t ht
    show log (0 + (135 / 16) * t) ^ 2 / t = log (t / (16 / 135)) ^ 2 / t
    rw [harg t]]
  rw [integral_logsq_ratio (16 / 135) (71 / 405) (by norm_num) (by norm_num)]

/-- B2b: `tripleTwo`'s affine logarithm is `log ((K-u)/(2a))`, `K = 71/135`, `a = 16/135`. -/
private theorem tripleTwo_eq :
    tripleTwo = (0.5617 * (135 / 32)) *
      (∫ u in (71 / 405 : ℝ)..(89 / 462 : ℝ),
        log ((71 / 135 - u) / (2 * (16 / 135))) ^ 2 / u) := by
  have harg : ∀ u : ℝ,
      (71 / 32 + (-135 / 32) * u) = (71 / 135 - u) / (2 * (16 / 135)) := by
    intro u; field_simp; ring
  unfold tripleTwo
  congr 1
  apply integral_congr
  intro u hu
  show log (71 / 32 + (-135 / 32) * u) ^ 2 / u
      = log ((71 / 135 - u) / (2 * (16 / 135))) ^ 2 / u
  rw [harg u]

/-- B2c: `tripleThree` is the band integral of the two elementary integrands. -/
private theorem tripleThree_eq :
    tripleThree = (0.5644 * (135 / 32)) *
      ((∫ u in (71 / 405 : ℝ)..(89 / 462 : ℝ), log (u / (16 / 135)) ^ 2 / u)
     - (∫ u in (71 / 405 : ℝ)..(89 / 462 : ℝ),
          log ((71 / 135 - u) / (2 * (16 / 135))) ^ 2 / u)) := by
  have harg1 : ∀ u : ℝ, (0 + (135 / 16) * u) = u / (16 / 135) := by
    intro u; field_simp; ring
  have harg2 : ∀ u : ℝ,
      (71 / 32 + (-135 / 32) * u) = (71 / 135 - u) / (2 * (16 / 135)) := by
    intro u; field_simp; ring
  unfold tripleThree
  congr 2
  · apply integral_congr
    intro u hu
    show log (0 + (135 / 16) * u) ^ 2 / u = log (u / (16 / 135)) ^ 2 / u
    rw [harg1 u]
  · apply integral_congr
    intro u hu
    show log (71 / 32 + (-135 / 32) * u) ^ 2 / u
        = log ((71 / 135 - u) / (2 * (16 / 135))) ^ 2 / u
    rw [harg2 u]


/-- B3: the limit constant `(135/16)*(0.5617*A + 0.5644*B)` of the model triple sum is
dominated by `tripleOne + tripleTwo + tripleThree`.  The two differ only by the
`89/462 - 1e-8` truncation of the exponent range (a shorter range, hence in our favour)
and by the band where the source uses the larger `0.5644`. -/
private theorem const_le :
    (135 / 16) * (0.5617 *
        ((1 / 2) * (∫ u in (16 / 135 : ℝ)..(71 / 405 : ℝ), log (u / (16 / 135)) ^ 2 / u)
       + (1 / 2) * (∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001 : ℝ),
            log ((71 / 135 - u) / (2 * (16 / 135))) ^ 2 / u))
      + 0.5644 *
        ((1 / 2) * (∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001 : ℝ),
            log (u / (16 / 135)) ^ 2 / u)
       - (1 / 2) * (∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001 : ℝ),
            log ((71 / 135 - u) / (2 * (16 / 135))) ^ 2 / u)))
    ≤ tripleOne + tripleTwo + tripleThree := by
  set J1 : ℝ := ∫ u in (16 / 135 : ℝ)..(71 / 405 : ℝ), log (u / (16 / 135)) ^ 2 / u with hJ1
  set J2 : ℝ := ∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001 : ℝ),
      log ((71 / 135 - u) / (2 * (16 / 135))) ^ 2 / u with hJ2
  set J3 : ℝ := ∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001 : ℝ),
      log (u / (16 / 135)) ^ 2 / u with hJ3
  set I2 : ℝ := ∫ u in (71 / 405 : ℝ)..(89 / 462 : ℝ),
      log ((71 / 135 - u) / (2 * (16 / 135))) ^ 2 / u with hI2
  set I3 : ℝ := ∫ u in (71 / 405 : ℝ)..(89 / 462 : ℝ),
      log (u / (16 / 135)) ^ 2 / u with hI3
  have hb : (89 / 462 - 0.00000001 : ℝ) ≤ 89 / 462 := by norm_num
  have hb2 : (71 / 405 : ℝ) ≤ 89 / 462 - 0.00000001 := by norm_num
  have hac : (16 / 135 : ℝ) ≤ 71 / 405 := by norm_num
  have hsubL : Set.Icc (89 / 462 - 0.00000001 : ℝ) (89 / 462)
      ⊆ Set.Icc (71 / 405 : ℝ) (89 / 462) :=
    Set.Icc_subset_Icc hb2 le_rfl
  have hsubL2 : Set.Icc (71 / 405 : ℝ) (89 / 462 - 0.00000001)
      ⊆ Set.Icc (71 / 405 : ℝ) (89 / 462) :=
    Set.Icc_subset_Icc le_rfl hb
  have hT1 : tripleOne = (0.5617 * (135 / 32)) * J1 := by
    rw [tripleOne_eq, hJ1, integral_logsq_ratio (16 / 135) (71 / 405) (by norm_num) (by norm_num)]
  have hT2 : tripleTwo = (0.5617 * (135 / 32)) * I2 := by
    rw [tripleTwo_eq]
  have hT3 : tripleThree = (0.5644 * (135 / 32)) * (I3 - I2) := by
    rw [tripleThree_eq]
  have hcL : ContinuousOn (fun u : ℝ => log (u / (16 / 135)) ^ 2 / u)
      (Set.Icc (71 / 405 : ℝ) (89 / 462)) := by
    apply ContinuousOn.div
    · apply ContinuousOn.pow
      apply ContinuousOn.log
      · fun_prop
      · intro u hu
        have h1 : (0 : ℝ) < u := by linarith [hu.1]
        exact div_ne_zero h1.ne' (by norm_num)
    · fun_prop
    · intro u hu
      have h1 : (0 : ℝ) < u := by linarith [hu.1]
      exact h1.ne'
  have hcM : ContinuousOn (fun u : ℝ => log ((71 / 135 - u) / (2 * (16 / 135))) ^ 2 / u)
      (Set.Icc (71 / 405 : ℝ) (89 / 462)) := by
    apply ContinuousOn.div
    · apply ContinuousOn.pow
      apply ContinuousOn.log
      · fun_prop
      · intro u hu
        exact (div_pos (by linarith [hu.2]) (by norm_num)).ne'
    · fun_prop
    · intro u hu
      have h1 : (0 : ℝ) < u := by linarith [hu.1]
      exact h1.ne'
  have hIntL : IntervalIntegrable (fun u : ℝ => log (u / (16 / 135)) ^ 2 / u)
      MeasureTheory.volume (71 / 405) (89 / 462 - 0.00000001) :=
    (hcL.mono hsubL2).intervalIntegrable_of_Icc hb2
  have hIntL2 : IntervalIntegrable (fun u : ℝ => log (u / (16 / 135)) ^ 2 / u)
      MeasureTheory.volume (89 / 462 - 0.00000001) (89 / 462) :=
    (hcL.mono hsubL).intervalIntegrable_of_Icc hb
  have hIntM : IntervalIntegrable (fun u : ℝ => log ((71 / 135 - u) / (2 * (16 / 135))) ^ 2 / u)
      MeasureTheory.volume (71 / 405) (89 / 462 - 0.00000001) :=
    (hcM.mono hsubL2).intervalIntegrable_of_Icc hb2
  have hIntM2 : IntervalIntegrable (fun u : ℝ => log ((71 / 135 - u) / (2 * (16 / 135))) ^ 2 / u)
      MeasureTheory.volume (89 / 462 - 0.00000001) (89 / 462) :=
    (hcM.mono hsubL).intervalIntegrable_of_Icc hb
  set x : ℝ := ∫ u in (89 / 462 - 0.00000001 : ℝ)..(89 / 462), log (u / (16 / 135)) ^ 2 / u with hxdef
  set m : ℝ := ∫ u in (89 / 462 - 0.00000001 : ℝ)..(89 / 462),
      log ((71 / 135 - u) / (2 * (16 / 135))) ^ 2 / u with hmdef
  have hX : I3 = J3 + x := by
    rw [hI3, hJ3, hxdef]
    exact (integral_add_adjacent_intervals hIntL hIntL2).symm
  have hM : I2 = J2 + m := by
    rw [hI2, hJ2, hmdef]
    exact (integral_add_adjacent_intervals hIntM hIntM2).symm
  have hx0 : 0 ≤ x := by
    rw [hxdef]
    apply integral_nonneg hb
    intro u hu
    exact div_nonneg (sq_nonneg _) (by linarith [hu.1])
  have hm0 : 0 ≤ m := by
    rw [hmdef]
    apply integral_nonneg hb
    intro u hu
    exact div_nonneg (sq_nonneg _) (by linarith [hu.1])
  have hmx : m ≤ x := by
    rw [hmdef, hxdef]
    refine intervalIntegral.integral_mono_on hb hIntM2 hIntL2 (fun u hu => ?_)
    have hu1 : (89 / 462 - 0.00000001 : ℝ) ≤ u := hu.1
    have hu2 : u ≤ 89 / 462 := hu.2
    have hpos : (0 : ℝ) < u := by linarith [hu1]
    have harg1 : 0 < (71 / 135 - u) / (2 * (16 / 135)) :=
      div_pos (by linarith [hu2]) (by norm_num)
    have hge1 : (1 : ℝ) ≤ (71 / 135 - u) / (2 * (16 / 135)) := by
      rw [le_div_iff₀ (by norm_num)]
      nlinarith [hu2]
    have hlog1 : 0 ≤ log ((71 / 135 - u) / (2 * (16 / 135))) := Real.log_nonneg hge1
    have hle : ((71 / 135 - u) / (2 * (16 / 135))) ≤ u / (16 / 135) := by
      rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
      nlinarith [hu1]
    have hlog2 : log ((71 / 135 - u) / (2 * (16 / 135))) ≤ log (u / (16 / 135)) :=
      Real.log_le_log harg1 hle
    have hpow := pow_le_pow_left₀ hlog1 hlog2 2
    exact div_le_div_of_nonneg_right hpow hpos.le
  rw [hT1, hT2, hT3, hX, hM]
  nlinarith [hx0, hm0, hmx]


end
end LeanLab.Languasco2004.Decomp578d



-- =====================================================================================
-- Pass `OMOS lomos 20261116T2320Z`(cont.): the inner `r`-sum at a fixed outer pair.
-- =====================================================================================

/-- C1: the innermost reciprocal prime sum of the triple model, for a fixed outer prime `q`.
`Σ_{α ≤ r < q, r prime} 1/r ≤ log (log q / log α) + 46 log 2 / (a log Y)` with `a = 16/135`.
This is `block_prime_mass_le` at `u = a`, `v = log q / log Y`, plus the one integer
`⌊Y^a⌋₊` that the model's non-strict left endpoint `α ≤ r` can add. -/
private theorem inner_r_le {Y : ℝ} {n q : ℕ} (hY : 1 < Y)
    (hα2 : 2 ≤ Y ^ (16 / 135 : ℝ))
    (hq : Y ^ (16 / 135 : ℝ) ≤ (q : ℝ))
    (hqb : (q : ℝ) ≤ Y ^ (89 / 462 - 0.00000001 : ℝ))
    (hbig : 2 * Real.log 2 ≤ (16 / 135) * Real.log Y) :
    (∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
        Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (q : ℝ)), (1 : ℝ) / (r : ℝ))
      ≤ Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y))
          + 46 * Real.log 2 / ((16 / 135) * Real.log Y) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have ha : (0 : ℝ) < 16 / 135 := by norm_num
  have hosp : (0 : ℝ) < (16 / 135) * Real.log Y := by positivity
  have hαpos : (0 : ℝ) < Y ^ (16 / 135 : ℝ) := Real.rpow_pos_of_pos hY0 _
  have hq2 : 2 ≤ q := by
    have h1 : (2 : ℝ) ≤ (q : ℝ) := le_trans hα2 hq
    exact_mod_cast h1
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have h : (0 : ℕ) < q := lt_of_lt_of_le (by norm_num) hq2
    exact_mod_cast h
  set v : ℝ := Real.log (q : ℝ) / Real.log Y with hv
  have hqlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hv1 : 16 / 135 ≤ v := by
    rw [hv, le_div_iff₀ hlogY]
    calc (16 / 135) * Real.log Y = Real.log (Y ^ (16 / 135 : ℝ)) := (Real.log_rpow hY0 _).symm
      _ ≤ Real.log (q : ℝ) := Real.log_le_log hαpos hq
  have hvb : v ≤ 89 / 462 - 0.00000001 := by
    rw [hv, div_le_iff₀ hlogY]
    calc Real.log (q : ℝ) ≤ Real.log (Y ^ (89 / 462 - 0.00000001 : ℝ)) :=
          Real.log_le_log hqpos hqb
      _ = (89 / 462 - 0.00000001) * Real.log Y := Real.log_rpow hY0 _
  have hYv : Y ^ v = (q : ℝ) := by
    rw [hv, Real.rpow_def_of_pos hY0, mul_div_cancel₀ _ hlogY.ne', Real.exp_log hqpos]
  have hfloorq : ⌊Y ^ v⌋₊ = q := by rw [hYv, Nat.floor_natCast]
  have hceil_le : ⌈Y ^ (16 / 135 : ℝ)⌉₊ ≤ q := by
    have h1 : ⌈Y ^ (16 / 135 : ℝ)⌉₊ ≤ ⌈(q : ℝ)⌉₊ := Nat.ceil_mono hq
    rwa [Nat.ceil_natCast] at h1
  have hne : ⌈Y ^ (16 / 135 : ℝ)⌉₊ ≤ ⌊Y ^ v⌋₊ := by rw [hfloorq]; exact hceil_le
  -- the block estimate
  have hblock := block_prime_mass_le (Y := Y) (u := 16 / 135) (v := v) hY le_rfl hv1 hvb hbig hne
  -- our set sits in that block plus the single integer `⌊Y^a⌋₊`
  have hsub : (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
        Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (q : ℝ))
      ⊆ insert ⌊Y ^ (16 / 135 : ℝ)⌋₊
          ((Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ v⌋₊).filter Nat.Prime) := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨-, hpr, hαr, hrq⟩ := hr
    rw [Finset.mem_insert]
    by_cases h : r = ⌊Y ^ (16 / 135 : ℝ)⌋₊
    · exact Or.inl h
    · refine Or.inr ?_
      have h1 : ⌊Y ^ (16 / 135 : ℝ)⌋₊ ≤ ⌊(r : ℝ)⌋₊ := Nat.floor_mono hαr
      rw [Nat.floor_natCast] at h1
      have hlt : ⌊Y ^ (16 / 135 : ℝ)⌋₊ < r := by omega
      have hrq' : r ≤ q := by
        have h2 : (r : ℝ) < (q : ℝ) := hrq
        have h3 : r < q := by exact_mod_cast h2
        omega
      rw [Finset.mem_filter, Finset.mem_Ioc, hfloorq]
      exact ⟨⟨hlt, hrq'⟩, hpr⟩
  have hsum_le : (∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
        Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (q : ℝ)), (1 : ℝ) / (r : ℝ))
      ≤ (1 : ℝ) / (⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℝ)
        + ∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ v⌋₊).filter Nat.Prime,
            (1 : ℝ) / (p : ℝ) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun x _ _ => by positivity)) ?_
    rw [Finset.sum_insert (by simp [Finset.mem_Ioc])]
  -- the single integer costs at most `2/(a log Y)`
  have hfloor_ge : Y ^ (16 / 135 : ℝ) / 2 ≤ (⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℝ) := by
    have h1 : Y ^ (16 / 135 : ℝ) - 1 < (⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℝ) := by
      have h := Nat.lt_floor_add_one (Y ^ (16 / 135 : ℝ))
      push_cast at h
      linarith
    linarith
  have hya : (16 / 135) * Real.log Y ≤ Y ^ (16 / 135 : ℝ) := by
    have h := Real.add_one_le_exp ((16 / 135) * Real.log Y)
    rw [Real.rpow_def_of_pos hY0, mul_comm (Real.log Y)]
    linarith
  have hrec : (1 : ℝ) / (⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℝ)
      ≤ 2 / ((16 / 135) * Real.log Y) := by
    have hfl : (0 : ℝ) < (⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℝ) := by linarith
    have h1 : (1 : ℝ) / (⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℝ) ≤ 1 / (Y ^ (16 / 135 : ℝ) / 2) := by
      apply one_div_le_one_div_of_le (by positivity) hfloor_ge
    have h2 : (1 : ℝ) / (Y ^ (16 / 135 : ℝ) / 2) = 2 / Y ^ (16 / 135 : ℝ) := by field_simp
    have h3 : (2 : ℝ) / Y ^ (16 / 135 : ℝ) ≤ 2 / ((16 / 135) * Real.log Y) := by
      apply div_le_div_of_nonneg_left (by norm_num) hosp hya
    linarith
  -- the logarithm transfer
  have hlogT : Real.log (v / (16 / 135))
      = Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y)) := by
    rw [hv]
    congr 1
    field_simp
  have hconst : (42 * Real.log 2 + 2) / ((16 / 135) * Real.log Y)
      ≤ 46 * Real.log 2 / ((16 / 135) * Real.log Y) := by
    have hl2 : (1 / 2 : ℝ) < Real.log 2 := by
      have h := Real.log_two_gt_d9
      linarith
    rw [div_le_div_iff₀ hosp hosp]
    nlinarith
  rw [← hlogT]
  have := hblock
  have := hsum_le
  have := hrec
  have h2 : (1 : ℝ) / (⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℝ) ≤ 2 / ((16 / 135) * Real.log Y) := hrec
  have h3 : (42 : ℝ) * Real.log 2 / ((16 / 135) * Real.log Y) + 2 / ((16 / 135) * Real.log Y)
      = (42 * Real.log 2 + 2) / ((16 / 135) * Real.log Y) := by field_simp
  linarith [hsum_le, hblock, hrec, hconst, h3]



-- =====================================================================================
-- C2: the model's pair sum, with the branch weight factored out of the inner `r`-sum.
-- =====================================================================================

/-- C2a: factor the branch weight out of the inner sum and split `1/(p q r)`. -/
private theorem model_eq_pair (Y : ℝ) (n : ℕ) :
    triplePrimeModel Y n = (135 / 16) * ∑ pq ∈ Source565.pairDomain true Y n,
      (if (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then (0.5617 : ℝ) else 0.5644)
        * ((1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
            * ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
                Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)), (1 : ℝ) / (r : ℝ)) := by
  unfold triplePrimeModel
  congr 1
  refine Finset.sum_congr rfl (fun pq hpq => ?_)
  rw [Source565.pairDomain, Finset.mem_filter] at hpq
  have hpp : pq.1.Prime := hpq.2.1
  have hqp : pq.2.Prime := hpq.2.2.2.2.1
  have hp0 : (pq.1 : ℝ) ≠ 0 := by
    have h : pq.1 ≠ 0 := hpp.ne_zero
    exact_mod_cast h
  have hq0 : (pq.2 : ℝ) ≠ 0 := by
    have h : pq.2 ≠ 0 := hqp.ne_zero
    exact_mod_cast h
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r hr => ?_)
  rw [Finset.mem_filter] at hr
  obtain ⟨hrp, hαr, hrq⟩ := hr.2
  have hr0 : (r : ℝ) ≠ 0 := by
    have h : r ≠ 0 := hrp.ne_zero
    exact_mod_cast h
  field_simp


/-- C2b: `0.5617 + 0.0027·[upper branch]` dominates the source weight, so the model is at most
`0.5617` times the full pair sum plus `0.0027` times the upper-branch pair sum. -/
private theorem model_le_branch (Y : ℝ) (n : ℕ) :
    triplePrimeModel Y n ≤ (135 / 16) *
      (0.5617 * (∑ pq ∈ Source565.pairDomain true Y n,
          (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
            * ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
                Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)), (1 : ℝ) / (r : ℝ))
      + 0.0027 * (∑ pq ∈ Source565.pairDomain true Y n,
          if (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0 else
            (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
              * ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
                  Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)), (1 : ℝ) / (r : ℝ))) := by
  rw [model_eq_pair]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun pq hpq => ?_)
  rw [Source565.pairDomain, Finset.mem_filter] at hpq
  have hpp : pq.1.Prime := hpq.2.1
  have hqp : pq.2.Prime := hpq.2.2.2.2.1
  have hp0 : (0 : ℝ) < (pq.1 : ℝ) := by exact_mod_cast hpp.pos
  have hq0 : (0 : ℝ) < (pq.2 : ℝ) := by exact_mod_cast hqp.pos
  have hM : 0 ≤ (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
      * ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
          Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)), (1 : ℝ) / (r : ℝ) := by
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro r _
    positivity
  split_ifs with h
  · linarith
  · linarith



/-- C3: the reciprocal pair sum over the source domain is bounded by `S²`, `S` the window
reciprocal-prime bound.  This is what absorbs the `O(1/log Y)` inner errors. -/
private theorem pair_recip_le {Y : ℝ} {n : ℕ} {S : ℝ} (hY : 1 < Y)
    (hS : (∑ p ∈ (Icc ⌈Y ^ (16 / 135 : ℝ)⌉₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
            (fun p : ℕ => p.Prime), (1 : ℝ) / (p : ℝ)) ≤ S) (hS0 : 0 ≤ S) :
    (∑ pq ∈ Source565.pairDomain true Y n, (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))) ≤ S * S := by
  set W : Finset ℕ := (Icc ⌈Y ^ (16 / 135 : ℝ)⌉₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
      (fun p : ℕ => p.Prime) with hW
  have hWsum : (∑ p ∈ W, (1 : ℝ) / (p : ℝ)) ≤ S := by rw [hW]; exact hS
  have hsub : Source565.pairDomain true Y n ⊆ W.product W := by
    intro pq hpq
    rw [Source565.pairDomain, Finset.mem_filter] at hpq
    obtain ⟨hpr, hαp, hsp, hqr, hαq, hqmin, hgrp, hdec, hβp⟩ := hpq.2
    have hqp : (pq.2 : ℝ) < (pq.1 : ℝ) := lt_of_lt_of_le hqmin (min_le_left _ _)
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · rw [hW, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨Nat.ceil_le.mpr hαp.le, Nat.le_floor (hβp rfl)⟩, hpr⟩
    · rw [hW, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.ceil_le.mpr hαq.le, Nat.le_floor ?_⟩, hqr⟩
      exact le_of_lt (lt_of_lt_of_le hqp (hβp rfl))
  calc (∑ pq ∈ Source565.pairDomain true Y n, (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ)))
      ≤ ∑ pq ∈ W.product W, (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => by positivity)
    _ = (∑ p ∈ W, (1 : ℝ) / (p : ℝ)) * (∑ p ∈ W, (1 : ℝ) / (p : ℝ)) := by
        rw [Finset.product_eq_sprod, Finset.sum_product, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun q hq => ?_))
        field_simp
    _ ≤ S * S := mul_le_mul hWsum hWsum (by positivity) hS0



/-- C4a: substitute the inner `r`-sum bound (C1) into the full pair sum, using C3 to absorb
the error. -/
private theorem pair_sum_le_log {Y : ℝ} {n : ℕ} {S : ℝ} (hY : 1 < Y)
    (hα2 : 2 ≤ Y ^ (16 / 135 : ℝ))
    (hbig : 2 * Real.log 2 ≤ (16 / 135) * Real.log Y)
    (hS : (∑ p ∈ (Icc ⌈Y ^ (16 / 135 : ℝ)⌉₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
            (fun p : ℕ => p.Prime), (1 : ℝ) / (p : ℝ)) ≤ S) (hS0 : 0 ≤ S) :
    (∑ pq ∈ Source565.pairDomain true Y n,
        (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
          * ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
              Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)), (1 : ℝ) / (r : ℝ))
      ≤ (∑ pq ∈ Source565.pairDomain true Y n,
          (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
            * Real.log (Real.log (pq.2 : ℝ) / ((16 / 135) * Real.log Y)))
        + 46 * Real.log 2 / ((16 / 135) * Real.log Y) * (S * S) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hpair := pair_recip_le (Y := Y) (n := n) (S := S) hY hS hS0
  have hpoint : ∀ pq ∈ Source565.pairDomain true Y n,
      (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
          * ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
              Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)), (1 : ℝ) / (r : ℝ)
        ≤ (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
            * (Real.log (Real.log (pq.2 : ℝ) / ((16 / 135) * Real.log Y))
                + 46 * Real.log 2 / ((16 / 135) * Real.log Y)) := by
    intro pq hpq
    rw [Source565.pairDomain, Finset.mem_filter] at hpq
    obtain ⟨hpr, hαp, hsp, hqr, hαq, hqmin, hgrp, hdec, hβp⟩ := hpq.2
    have hqp : (pq.2 : ℝ) < (pq.1 : ℝ) := lt_of_lt_of_le hqmin (min_le_left _ _)
    have hqα : Y ^ (16 / 135 : ℝ) ≤ (pq.2 : ℝ) := le_of_lt hαq
    have hqβ : (pq.2 : ℝ) ≤ Y ^ (89 / 462 - 0.00000001 : ℝ) :=
      le_of_lt (lt_of_lt_of_le hqp (hβp rfl))
    have hbound := inner_r_le (Y := Y) (n := n) (q := pq.2) hY hα2 hqα hqβ hbig
    exact mul_le_mul_of_nonneg_left hbound (div_nonneg zero_le_one (by positivity))
  refine le_trans (Finset.sum_le_sum hpoint) ?_
  have hsplit : ∀ pq : ℕ × ℕ,
      (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
          * (Real.log (Real.log (pq.2 : ℝ) / ((16 / 135) * Real.log Y))
              + 46 * Real.log 2 / ((16 / 135) * Real.log Y))
        = (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
            * Real.log (Real.log (pq.2 : ℝ) / ((16 / 135) * Real.log Y))
          + 46 * Real.log 2 / ((16 / 135) * Real.log Y)
              * ((1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))) := by
    intro pq; ring
  simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  refine add_le_add le_rfl ?_
  exact mul_le_mul_of_nonneg_left hpair (by positivity)



/-- C4b: the same substitution on the upper branch `p q² > Y^(71/135)`. -/
private theorem pair_sum_le_log_upper {Y : ℝ} {n : ℕ} {S : ℝ} (hY : 1 < Y)
    (hα2 : 2 ≤ Y ^ (16 / 135 : ℝ))
    (hbig : 2 * Real.log 2 ≤ (16 / 135) * Real.log Y)
    (hS : (∑ p ∈ (Icc ⌈Y ^ (16 / 135 : ℝ)⌉₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
            (fun p : ℕ => p.Prime), (1 : ℝ) / (p : ℝ)) ≤ S) (hS0 : 0 ≤ S) :
    (∑ pq ∈ Source565.pairDomain true Y n,
        if (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0 else
          (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
            * ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
                Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)), (1 : ℝ) / (r : ℝ))
      ≤ (∑ pq ∈ Source565.pairDomain true Y n,
          if (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0 else
            (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
              * Real.log (Real.log (pq.2 : ℝ) / ((16 / 135) * Real.log Y)))
        + 46 * Real.log 2 / ((16 / 135) * Real.log Y) * (S * S) := by
  have hpair := pair_recip_le (Y := Y) (n := n) (S := S) hY hS hS0
  have hpairif : (∑ pq ∈ Source565.pairDomain true Y n,
      if (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0 else
        (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))) ≤ S * S := by
    refine le_trans (Finset.sum_le_sum (fun pq _ => ?_)) hpair
    split_ifs with h
    · exact div_nonneg zero_le_one (by positivity)
    · exact le_rfl
  have hpoint : ∀ pq ∈ Source565.pairDomain true Y n,
      (if (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0 else
          (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
            * ∑ r ∈ (range (n + 1)).filter (fun r : ℕ => r.Prime ∧
                Y ^ (16 / 135 : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) < (pq.2 : ℝ)), (1 : ℝ) / (r : ℝ))
        ≤ (if (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0 else
            (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
              * (Real.log (Real.log (pq.2 : ℝ) / ((16 / 135) * Real.log Y))
                  + 46 * Real.log 2 / ((16 / 135) * Real.log Y))) := by
    intro pq hpq
    split_ifs with h
    · exact le_rfl
    · rw [Source565.pairDomain, Finset.mem_filter] at hpq
      obtain ⟨hpr, hαp, hsp, hqr, hαq, hqmin, hgrp, hdec, hβp⟩ := hpq.2
      have hqp : (pq.2 : ℝ) < (pq.1 : ℝ) := lt_of_lt_of_le hqmin (min_le_left _ _)
      have hqα : Y ^ (16 / 135 : ℝ) ≤ (pq.2 : ℝ) := le_of_lt hαq
      have hqβ : (pq.2 : ℝ) ≤ Y ^ (89 / 462 - 0.00000001 : ℝ) :=
        le_of_lt (lt_of_lt_of_le hqp (hβp rfl))
      have hbound := inner_r_le (Y := Y) (n := n) (q := pq.2) hY hα2 hqα hqβ hbig
      exact mul_le_mul_of_nonneg_left hbound (div_nonneg zero_le_one (by positivity))
  refine le_trans (Finset.sum_le_sum hpoint) ?_
  have hsplit : ∀ pq : ℕ × ℕ,
      (if (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0 else
          (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
            * (Real.log (Real.log (pq.2 : ℝ) / ((16 / 135) * Real.log Y))
                + 46 * Real.log 2 / ((16 / 135) * Real.log Y)))
        = (if (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0 else
            (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
              * Real.log (Real.log (pq.2 : ℝ) / ((16 / 135) * Real.log Y)))
          + 46 * Real.log 2 / ((16 / 135) * Real.log Y)
              * (if (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0 else
                  (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))) := by
    intro pq
    split_ifs with h <;> ring
  simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hpairif
      (by apply div_nonneg
          · have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
            nlinarith
          · have hl := Real.log_pos hY
            nlinarith))



/-- C5: the lower mirror of `block_prime_mass_le`: the reciprocal mass of a block is at least
its Mertens main term minus the deviation.  Here the deviation window sits *inside* the block,
so no single-integer correction is needed. -/
private theorem block_prime_mass_ge {Y u v : ℝ} (hY : 1 < Y)
    (hu1 : 16 / 135 ≤ u) (huv : u ≤ v) (hv2 : v ≤ 89 / 462 - 0.00000001)
    (hbig : 2 * Real.log 2 ≤ (16 / 135) * Real.log Y)
    (hne : ⌈Y ^ u⌉₊ ≤ ⌊Y ^ v⌋₊) :
    Real.log (v / u) - 42 * Real.log 2 / ((16 / 135) * Real.log Y)
      ≤ ∑ p ∈ (Ioc ⌊Y ^ u⌋₊ ⌊Y ^ v⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have ha : (0 : ℝ) < 16 / 135 := by norm_num
  have hu0 : 0 < u := lt_of_lt_of_le ha hu1
  have haY : (0 : ℝ) < (16 / 135) * Real.log Y := by positivity
  have huY : (0 : ℝ) < u * Real.log Y := by positivity
  have hdev := prime_window_deviation (Y := Y) (x1 := u) (x2 := v) hY hu0 huv hu1 hv2
    (le_trans hbig (by nlinarith [hu1, hlogY])) hne
  obtain ⟨hlo, hhi⟩ := abs_le.mp hdev
  have hflo : ⌊Y ^ u⌋₊ ≤ ⌈Y ^ u⌉₊ := by
    have h1 : (⌊Y ^ u⌋₊ : ℝ) ≤ (⌈Y ^ u⌉₊ : ℝ) :=
      le_trans (Nat.floor_le (by positivity)) (Nat.le_ceil _)
    exact_mod_cast h1
  have hsub : (Ioc ⌈Y ^ u⌉₊ ⌊Y ^ v⌋₊).filter Nat.Prime
      ⊆ (Ioc ⌊Y ^ u⌋₊ ⌊Y ^ v⌋₊).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpmem, hpp⟩ := Finset.mem_filter.mp hp
    rw [Finset.mem_Ioc] at hpmem
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨lt_of_le_of_lt hflo hpmem.1, hpmem.2⟩, hpp⟩
  have h1 : 40 * Real.log 2 / (u * Real.log Y)
      ≤ 42 * Real.log 2 / ((16 / 135) * Real.log Y) := by
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hpos2 : 0 < Real.log 2 * Real.log Y := mul_pos hl2 hlogY
    have hstep : 40 * (16 / 135) ≤ 42 * u := by nlinarith [hu1]
    have hmul : (Real.log 2 * Real.log Y) * (40 * (16 / 135))
        ≤ (Real.log 2 * Real.log Y) * (42 * u) :=
      mul_le_mul_of_nonneg_left hstep hpos2.le
    rw [div_le_div_iff₀ huY haY]
    nlinarith [hmul]
  have h2 : Real.log (v / u) - 42 * Real.log 2 / ((16 / 135) * Real.log Y)
      ≤ ∑ p ∈ (Ioc ⌈Y ^ u⌉₊ ⌊Y ^ v⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
    linarith
  exact le_trans h2 (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => by positivity))



/-- C6: the lower mirror of `prime_sum_block_le`: for increasing nonnegative `φ` the block
comparison also bounds the prime sum from below.  Needed to subtract the capped `q`-range
(the upper branch `p q² > Y^(71/135)` is the full range minus the capped one). -/
private theorem prime_sum_block_ge
    {Y : ℝ} (hY : 1 < Y) {K : ℕ} (hK : 0 < K) {μ : ℝ}
    (hμ1 : 16 / 135 ≤ μ) (hμ2 : μ ≤ 89 / 462 - 0.00000001)
    (hbig : 2 * Real.log 2 ≤ (16 / 135) * Real.log Y)
    (φ : ℝ → ℝ)
    (hmono : ∀ x y : ℝ, 16 / 135 ≤ x → x ≤ y → y ≤ μ → φ x ≤ φ y)
    (hφnn : ∀ x : ℝ, 16 / 135 ≤ x → x ≤ μ → 0 ≤ φ x)
    (hint : ∀ u v : ℝ, 16 / 135 ≤ u → u ≤ v → v ≤ μ →
      IntervalIntegrable (fun x : ℝ => φ x / x) MeasureTheory.volume u v)
    (hne : ∀ i : ℕ, i < K →
      ⌈Y ^ (16 / 135 + (i : ℝ) * ((μ - 16 / 135) / (K : ℝ)))⌉₊
        ≤ ⌊Y ^ (16 / 135 + ((i : ℝ) + 1) * ((μ - 16 / 135) / (K : ℝ)))⌋₊) :
    (∫ x in (16 / 135)..μ, φ x / x)
        - φ μ * ((μ - 16 / 135) / ((16 / 135) * (K : ℝ))
            + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)))
      ≤ (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ μ⌋₊).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ) * φ (Real.log (p : ℝ) / Real.log Y)) := by
  have hY0 : 0 < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have ha : (0 : ℝ) < 16 / 135 := by norm_num
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  set w : ℝ := (μ - 16 / 135) / (K : ℝ) with hw
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  set c : ℕ → ℝ := fun i => 16 / 135 + (i : ℝ) * w with hc
  have hc0 : c 0 = 16 / 135 := by simp [hc]
  have hcK : c K = μ := by
    rw [hc, hw]; push_cast; field_simp; ring
  have hcmono : ∀ i : ℕ, c i ≤ c (i + 1) := by
    intro i; rw [hc]; push_cast; nlinarith [hw0]
  have hci_ge : ∀ i : ℕ, 16 / 135 ≤ c i := by
    intro i
    rw [hc]
    have h0 : (0 : ℝ) ≤ (i : ℝ) * w := by positivity
    linarith
  have hci_mono_le : ∀ i : ℕ, i ≤ K → c i ≤ μ := by
    intro i hi
    calc c i = c K + (c i - c K) := by ring
      _ ≤ c K := by
          rw [hc]; push_cast
          have h1 : (i : ℝ) * w ≤ (K : ℝ) * w := by
            apply mul_le_mul_of_nonneg_right _ hw0
            exact_mod_cast hi
          linarith
      _ = μ := hcK
  set n : ℕ → ℕ := fun i => ⌊Y ^ c i⌋₊ with hn
  have hnmono : ∀ i, i < K → n i ≤ n (i + 1) := by
    intro i _
    rw [hn]
    exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hY.le (hcmono i))
  have hblock : ∀ i, i < K →
      (Real.log (c (i + 1) / c i) - 42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ (c i)
        ≤ (∑ p ∈ (Ioc (n i) (n (i + 1))).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ) * φ (Real.log (p : ℝ) / Real.log Y)) := by
    intro i hi
    have hci : 16 / 135 ≤ c i := hci_ge i
    have hci1le : c (i + 1) ≤ μ := hci_mono_le (i + 1) hi
    have hcin : (0 : ℝ) ≤ φ (c i) := hφnn _ hci (le_trans (hcmono i) hci1le)
    have hne' : ⌈Y ^ c i⌉₊ ≤ ⌊Y ^ c (i + 1)⌋₊ := by
      rw [hc, hw]; push_cast; exact hne i hi
    have hmass := block_prime_mass_ge (Y := Y) (u := c i) (v := c (i + 1)) hY hci
      (hcmono i) (le_trans hci1le hμ2) (le_trans hbig (by nlinarith [hci, hlogY])) hne'
    have hpt : ∀ p ∈ (Ioc (n i) (n (i + 1))).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ) * φ (c i)
          ≤ (1 : ℝ) / (p : ℝ) * φ (Real.log (p : ℝ) / Real.log Y) := by
      intro p hp
      obtain ⟨hpmem, hpp⟩ := Finset.mem_filter.mp hp
      rw [Finset.mem_Ioc] at hpmem
      have hlow : c i < Real.log (p : ℝ) / Real.log Y := by
        have h1 : Y ^ c i < (p : ℝ) := by
          have h2 := Nat.lt_floor_add_one (Y ^ c i)
          have h5 : ⌊Y ^ c i⌋₊ < p := by simpa only [hn] using hpmem.1
          have h3 : ((⌊Y ^ c i⌋₊ : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by
            exact_mod_cast Nat.succ_le_of_lt h5
          linarith
        have h4 := Real.log_lt_log (Real.rpow_pos_of_pos hY0 (c i)) h1
        rw [Real.log_rpow hY0] at h4
        rw [lt_div_iff₀ hlogY]
        linarith
      have hp2 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
      have hhigh : Real.log (p : ℝ) / Real.log Y ≤ c (i + 1) := by
        have h1 : (p : ℝ) ≤ Y ^ c (i + 1) := by
          have h2 : p ≤ n (i + 1) := hpmem.2
          have h3 : ((n (i + 1) : ℕ) : ℝ) ≤ Y ^ c (i + 1) := by
            rw [hn]
            exact Nat.floor_le (by positivity)
          exact le_trans (by exact_mod_cast h2) h3
        have h4 := Real.log_le_log hp2 h1
        rw [Real.log_rpow hY0] at h4
        rw [div_le_iff₀ hlogY]
        linarith
      have hstep : φ (c i) ≤ φ (Real.log (p : ℝ) / Real.log Y) :=
        hmono _ _ hci hlow.le (le_trans hhigh hci1le)
      exact mul_le_mul_of_nonneg_left hstep (by positivity)
    calc (Real.log (c (i + 1) / c i) - 42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ (c i)
        ≤ (∑ p ∈ (Ioc (n i) (n (i + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) * φ (c i) :=
          mul_le_mul_of_nonneg_right hmass hcin
      _ = ∑ p ∈ (Ioc (n i) (n (i + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ) * φ (c i) := by
          rw [Finset.sum_mul]
      _ ≤ ∑ p ∈ (Ioc (n i) (n (i + 1))).filter Nat.Prime,
            (1 : ℝ) / (p : ℝ) * φ (Real.log (p : ℝ) / Real.log Y) := Finset.sum_le_sum hpt
  -- the block integral is at most the upper staircase value
  have hInt : ∀ i, i < K →
      (∫ x in (c i)..(c (i + 1)), φ x / x)
        ≤ φ (c (i + 1)) * Real.log (c (i + 1) / c i) := by
    intro i hi
    have hci : 16 / 135 ≤ c i := hci_ge i
    have hci0 : (0 : ℝ) < c i := lt_of_lt_of_le ha hci
    have hci1le : c (i + 1) ≤ μ := hci_mono_le (i + 1) hi
    have hle := hcmono i
    have h1 : (∫ x in (c i)..(c (i + 1)), φ x / x)
        ≤ ∫ x in (c i)..(c (i + 1)), φ (c (i + 1)) / x := by
      apply integral_mono_on hle (hint (c i) (c (i + 1)) hci hle hci1le)
      · apply ContinuousOn.intervalIntegrable_of_Icc hle
        apply ContinuousOn.div continuousOn_const continuousOn_id
        intro x hx
        exact ne_of_gt (lt_of_lt_of_le hci0 hx.1)
      · intro x hx
        have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hci0 hx.1
        have hstep : φ x ≤ φ (c (i + 1)) :=
          hmono _ _ (le_trans hci hx.1) hx.2 hci1le
        exact div_le_div_of_nonneg_right hstep hx0.le
    have hci1pos : (0 : ℝ) < c (i + 1) := lt_of_lt_of_le hci0 hle
    have h2 : (∫ x in (c i)..(c (i + 1)), φ (c (i + 1)) / x)
        = φ (c (i + 1)) * Real.log (c (i + 1) / c i) := by
      have hA : (∫ x in (c i)..(c (i + 1)), φ (c (i + 1)) / x)
          = φ (c (i + 1)) * ∫ x in (c i)..(c (i + 1)), 1 / x := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x _
        simp only [div_eq_mul_inv, one_mul]
      rw [hA, integral_one_div_of_pos hci0 hci1pos]
    linarith [h1, h2]
  have hlogratio : ∀ i, i < K → Real.log (c (i + 1) / c i) ≤ w / (16 / 135) := by
    intro i hi
    have hci : 16 / 135 ≤ c i := hci_ge i
    have hci0 : (0 : ℝ) < c i := lt_of_lt_of_le ha hci
    have hstep : c (i + 1) / c i = 1 + w / c i := by
      rw [hc]; push_cast; field_simp; ring
    rw [hstep]
    calc Real.log (1 + w / c i) ≤ 1 + w / c i - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ = w / c i := by ring
      _ ≤ w / (16 / 135) := div_le_div_of_nonneg_left hw0 ha hci
  have hdiff : ∀ i, i < K → (0 : ℝ) ≤ φ (c (i + 1)) - φ (c i) := by
    intro i hi
    have hci : 16 / 135 ≤ c i := hci_ge i
    have hci1le : c (i + 1) ≤ μ := hci_mono_le (i + 1) hi
    have := hmono _ _ hci (hcmono i) hci1le
    linarith
  have htele2 : (∑ i ∈ Finset.range K, (φ (c (i + 1)) - φ (c i))) = φ (c K) - φ (c 0) := by
    rw [← Nat.Ico_zero_eq_range]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (sum_Ico_sub (fun i : ℕ => φ (c i)) (Nat.zero_le K))
  have hphi0 : (0 : ℝ) ≤ φ (16 / 135) := hφnn _ le_rfl hμ1
  -- termwise lower bound on the block coefficient
  have hterm : ∀ i, i < K →
      (∫ x in (c i)..(c (i + 1)), φ x / x)
        - (w / (16 / 135)) * (φ (c (i + 1)) - φ (c i))
        - (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ μ
        ≤ (Real.log (c (i + 1) / c i) - 42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ (c i) := by
    intro i hi
    have hci : 16 / 135 ≤ c i := hci_ge i
    have hci1le : c (i + 1) ≤ μ := hci_mono_le (i + 1) hi
    have hIi := hInt i hi
    have hLi := hlogratio i hi
    have hdi := hdiff i hi
    have hnn : (0 : ℝ) ≤ φ (c (i + 1)) := hφnn _ (le_trans hci (hcmono i)) hci1le
    have hphile : φ (c i) ≤ φ μ := hmono _ _ hci (le_trans (hcmono i) hci1le) le_rfl
    have hwL : (φ (c (i + 1)) - φ (c i)) * Real.log (c (i + 1) / c i)
        ≤ (φ (c (i + 1)) - φ (c i)) * (w / (16 / 135)) :=
      mul_le_mul_of_nonneg_left hLi hdi
    have heta : (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ (c i)
        ≤ (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ μ :=
      mul_le_mul_of_nonneg_left hphile (by positivity)
    have hbody : (Real.log (c (i + 1) / c i) - 42 * Real.log 2 / ((16 / 135) * Real.log Y))
          * φ (c i)
        = φ (c (i + 1)) * Real.log (c (i + 1) / c i)
          - (φ (c (i + 1)) - φ (c i)) * Real.log (c (i + 1) / c i)
          - (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ (c i) := by ring
    linarith [hIi, hwL, heta, hbody]
  -- assemble
  have hsumge : (∑ i ∈ Finset.range K,
        ((∫ x in (c i)..(c (i + 1)), φ x / x)
          - (w / (16 / 135)) * (φ (c (i + 1)) - φ (c i))
          - (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ μ))
      ≤ ∑ i ∈ Finset.range K,
          (Real.log (c (i + 1) / c i) - 42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ (c i) :=
    Finset.sum_le_sum (fun i hi => hterm i (Finset.mem_range.mp hi))
  have hsplit : (∑ i ∈ Finset.range K,
        ((∫ x in (c i)..(c (i + 1)), φ x / x)
          - (w / (16 / 135)) * (φ (c (i + 1)) - φ (c i))
          - (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ μ))
      = (∑ i ∈ Finset.range K, ∫ x in (c i)..(c (i + 1)), φ x / x)
        - (w / (16 / 135)) * (∑ i ∈ Finset.range K, (φ (c (i + 1)) - φ (c i)))
        - (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ μ := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hItel : (∑ i ∈ Finset.range K, ∫ x in (c i)..(c (i + 1)), φ x / x)
      = ∫ x in (16 / 135)..μ, φ x / x := by
    have := intervalIntegral.sum_integral_adjacent_intervals
      (f := fun x : ℝ => φ x / x) (a := c) (n := K)
      (fun k hk => hint (c k) (c (k + 1)) (by
        rw [hc]
        have : (0 : ℝ) ≤ (k : ℝ) * w := by positivity
        linarith) (hcmono k) (by
        have hik : ((k : ℝ) + 1) ≤ (K : ℝ) := by
          have : k + 1 ≤ K := hk
          exact_mod_cast this
        calc c (k + 1) = c K + (c (k + 1) - c K) := by ring
          _ ≤ c K := by
              rw [hc]; push_cast
              have h1 : ((k : ℝ) + 1) * w ≤ (K : ℝ) * w :=
                mul_le_mul_of_nonneg_right hik hw0
              linarith
          _ = μ := hcK))
    rw [hc0, hcK] at this
    exact this
  have hD : (∑ i ∈ Finset.range K, (φ (c (i + 1)) - φ (c i))) ≤ φ μ := by
    rw [htele2, hc0, hcK]
    linarith [hphi0]
  have hDnn : (0 : ℝ) ≤ w / (16 / 135) := by positivity
  have htele := prime_sum_telescope
    (f := fun p => (1 : ℝ) / (p : ℝ) * φ (Real.log (p : ℝ) / Real.log Y)) n K hnmono
  have hn0' : n 0 = ⌊Y ^ (16 / 135 : ℝ)⌋₊ := by
    simp only [hn]
    exact congrArg (fun z : ℝ => ⌊Y ^ z⌋₊) hc0
  have hnK' : n K = ⌊Y ^ μ⌋₊ := by
    simp only [hn]
    exact congrArg (fun z : ℝ => ⌊Y ^ z⌋₊) hcK
  have htele' : (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ μ⌋₊).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ) * φ (Real.log (p : ℝ) / Real.log Y))
      = ∑ i ∈ Finset.range K, ∑ p ∈ (Ioc (n i) (n (i + 1))).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ) * φ (Real.log (p : ℝ) / Real.log Y) := by
    rw [← hn0', ← hnK']
    exact htele
  have hlow : (∫ x in (16 / 135)..μ, φ x / x)
        - φ μ * ((μ - 16 / 135) / ((16 / 135) * (K : ℝ))
            + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)))
      ≤ ∑ i ∈ Finset.range K,
          (Real.log (c (i + 1) / c i) - 42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ (c i) := by
    have hm := mul_le_mul_of_nonneg_left hD hDnn
    have hw' : w / (16 / 135) = (μ - 16 / 135) / ((16 / 135) * (K : ℝ)) := by
      rw [hw]; field_simp; try ring
    rw [hsplit, hItel] at hsumge
    rw [hw'] at hsumge hm
    have hkey : φ μ * ((μ - 16 / 135) / ((16 / 135) * (K : ℝ))
          + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)))
        = φ μ * ((μ - 16 / 135) / ((16 / 135) * (K : ℝ)))
          + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)) * φ μ := by ring
    rw [hkey]
    have hcomm : (μ - 16 / 135) / ((16 / 135) * (K : ℝ)) * φ μ
        = φ μ * ((μ - 16 / 135) / ((16 / 135) * (K : ℝ))) := by ring
    linarith [hsumge, hm, hcomm]
  rw [htele']
  refine le_trans hlow (Finset.sum_le_sum (fun i hi => hblock i (Finset.mem_range.mp hi)))



/-- C7: the lower mirror of `inner_q_sum_le` — the same inner `q`-sum with weight `log(y/a)`
is also bounded *below* by the continuous value minus the staircase and Mertens errors.
Needed because the upper branch `p q² > Y^(71/135)` is the full `q`-range minus a capped range. -/
private theorem inner_q_sum_ge {Y : ℝ} (hY : 1 < Y) {K : ℕ} (hK : 0 < K) {μ : ℝ}
    (hμ1 : 16 / 135 ≤ μ) (hμ2 : μ ≤ 89 / 462 - 0.00000001)
    (hbig : 2 * Real.log 2 ≤ (16 / 135) * Real.log Y)
    (hne : ∀ i : ℕ, i < K →
      ⌈Y ^ (16 / 135 + (i : ℝ) * ((μ - 16 / 135) / (K : ℝ)))⌉₊
        ≤ ⌊Y ^ (16 / 135 + ((i : ℝ) + 1) * ((μ - 16 / 135) / (K : ℝ)))⌋₊) :
    (1 / 2) * Real.log (μ / (16 / 135)) ^ 2
        - Real.log (μ / (16 / 135))
            * ((μ - 16 / 135) / ((16 / 135) * (K : ℝ))
                + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)))
      ≤ (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ μ⌋₊).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ) * Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135))) := by
  have hY0 : 0 < Y := by linarith
  have ha : (0 : ℝ) < 16 / 135 := by norm_num
  have hmain := prime_sum_block_ge (Y := Y) (K := K) (μ := μ) hY hK hμ1 hμ2 hbig
    (fun y : ℝ => Real.log (y / (16 / 135)))
    (fun x y hx hxy hy => by
      apply Real.log_le_log (by linarith)
      exact div_le_div_of_nonneg_right hxy (by norm_num))
    (fun x hx _ => Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith))
    (fun u v hu huv hv => by
      apply ContinuousOn.intervalIntegrable_of_Icc huv
      have hu0 : (0 : ℝ) < u := lt_of_lt_of_le ha hu
      have hne0 : ∀ x ∈ Set.Icc u v, x ≠ 0 := by
        intro x hx
        have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hu0 hx.1
        linarith
      have hpos : ∀ x ∈ Set.Icc u v, x / (16 / 135) ≠ 0 := by
        intro x hx
        have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hu0 hx.1
        exact div_ne_zero (ne_of_gt hx0) (by norm_num)
      exact (ContinuousOn.log (by fun_prop) hpos).div continuousOn_id hne0)
    hne
  have hint : (∫ x in (16 / 135)..μ, Real.log (x / (16 / 135)) / x)
      = Real.log (μ / (16 / 135)) ^ 2 / 2 :=
    Integral565.integral_log_ratio (16 / 135) μ ha hμ1
  rw [hint] at hmain
  linarith [hmain]



/-- C8: a Finset tool.  If `s ⊆ insert q0 t` and `f` is nonnegative on `t` while `f q0 ≤ 0`,
then `Σ_s f ≤ Σ_t f`.  This is how the model's *non-strict* left endpoint `α ≤ r` / `α ≤ q`
is absorbed without a case split at every use site. -/
private theorem sum_le_of_subset_insert {s t : Finset ℕ} {q0 : ℕ} {f : ℕ → ℝ}
    (hsub : s ⊆ insert q0 t) (hq0 : f q0 ≤ 0) (hpos : ∀ x ∈ t, 0 ≤ f x) :
    ∑ x ∈ s, f x ≤ ∑ x ∈ t, f x := by
  by_cases h : q0 ∈ s
  · have herase : s.erase q0 ⊆ t := by
      intro x hx
      have hxs : x ∈ s := Finset.mem_of_mem_erase hx
      have hne : x ≠ q0 := Finset.ne_of_mem_erase hx
      rcases Finset.mem_insert.mp (hsub hxs) with h' | h'
      · exact absurd h' hne
      · exact h'
    have h1 : ∑ x ∈ s.erase q0, f x ≤ ∑ x ∈ t, f x :=
      Finset.sum_le_sum_of_subset_of_nonneg herase (fun x hx _ => hpos x hx)
    have h2 : ∑ x ∈ s.erase q0, f x + f q0 = ∑ x ∈ s, f x :=
      Finset.sum_erase_add s f h
    linarith
  · have hst : s ⊆ t := by
      intro x hx
      rcases Finset.mem_insert.mp (hsub hx) with h' | h'
      · exact absurd (h'.symm ▸ hx) h
      · exact h'
    exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun x hx _ => hpos x hx)


/-- C9: the per-outer-prime cap reduction for the **sharp** branch.
For a fixed outer prime `p`, the inner `q`-sum restricted to `p q² ≤ Y^(71/135)` is at most the
`inner_q_sum_le` bound at the cap `μ = min(log p/log Y, (71/135 − log p/log Y)/2)`.  The model's
non-strict endpoint `Y^(16/135) ≤ q` costs nothing: the only prime it can add below the
`inner_q_sum_le` window is `⌊Y^(16/135)⌋₊`, where the weight is `≤ 0`. -/
private theorem inner_q_cut_le {Y : ℝ} {n p : ℕ} {K : ℕ} {μ : ℝ} (hY : 1 < Y) (hK : 0 < K)
    (hp : p.Prime)
    (hμdef : μ = min (Real.log (p : ℝ) / Real.log Y)
      ((71 / 135 - Real.log (p : ℝ) / Real.log Y) / 2))
    (hμ1 : 16 / 135 ≤ μ) (hμ2 : μ ≤ 89 / 462 - 0.00000001)
    (hbig : 2 * Real.log 2 ≤ (16 / 135) * Real.log Y)
    (hne : ∀ i : ℕ, i < K →
      ⌈Y ^ (16 / 135 + (i : ℝ) * ((μ - 16 / 135) / (K : ℝ)))⌉₊
        ≤ ⌊Y ^ (16 / 135 + ((i : ℝ) + 1) * ((μ - 16 / 135) / (K : ℝ)))⌋₊) :
    (∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
        Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ) ∧
        (p : ℝ) * (q : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ)),
        (1 / (q : ℝ)) * Real.log (Real.log (q : ℝ) / Real.log Y / (16 / 135)))
      ≤ (1 / 2) * Real.log (μ / (16 / 135)) ^ 2
        + Real.log (μ / (16 / 135))
            * ((μ - 16 / 135) / ((16 / 135) * (K : ℝ))
                + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y))) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have ha : (0 : ℝ) < 16 / 135 := by norm_num
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  -- the containment into `insert ⌊Y^a⌋ (window)`
  have hsub : (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
        Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ) ∧
        (p : ℝ) * (q : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ))
      ⊆ insert ⌊Y ^ (16 / 135 : ℝ)⌋₊
          ((Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ μ⌋₊).filter Nat.Prime) := by
    intro q hq
    obtain ⟨-, hqp, hαq, hqlt, hbranch⟩ := Finset.mem_filter.mp hq
    have hqpos : (0 : ℝ) < (q : ℝ) := by
      have h : (0 : ℕ) < q := lt_of_lt_of_le (by norm_num) hqp.two_le
      exact_mod_cast h
    rw [Finset.mem_insert]
    by_cases h : q = ⌊Y ^ (16 / 135 : ℝ)⌋₊
    · exact Or.inl h
    · refine Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hqp⟩)
      · -- `⌊Y^a⌋ < q`
        have h1 : ⌊Y ^ (16 / 135 : ℝ)⌋₊ ≤ ⌊(q : ℝ)⌋₊ := Nat.floor_mono hαq
        rw [Nat.floor_natCast] at h1
        omega
      · -- `q ≤ ⌊Y^μ⌋`
        have hyx : Real.log (q : ℝ) / Real.log Y < Real.log (p : ℝ) / Real.log Y := by
          have hlt : (q : ℝ) < (p : ℝ) := hqlt
          exact div_lt_div_of_pos_right (Real.log_lt_log hqpos hlt) hlogY
        have hycap : Real.log (q : ℝ) / Real.log Y
            ≤ (71 / 135 - Real.log (p : ℝ) / Real.log Y) / 2 := by
          have hpos2 : (0 : ℝ) < (p : ℝ) * (q : ℝ) ^ 2 := by positivity
          have h1 : Real.log ((p : ℝ) * (q : ℝ) ^ 2) ≤ (71 / 135) * Real.log Y := by
            calc Real.log ((p : ℝ) * (q : ℝ) ^ 2) ≤ Real.log (Y ^ (71 / 135 : ℝ)) :=
                  Real.log_le_log hpos2 hbranch
              _ = (71 / 135) * Real.log Y := Real.log_rpow hY0 _
          have h2 : Real.log ((p : ℝ) * (q : ℝ) ^ 2)
              = Real.log (p : ℝ) + 2 * Real.log (q : ℝ) := by
            rw [Real.log_mul hp0.ne' (by positivity), Real.log_pow]
            push_cast
            ring
          rw [h2] at h1
          rw [le_div_iff₀ (by norm_num)]
          have h3 : Real.log (q : ℝ) / Real.log Y * 2 + Real.log (p : ℝ) / Real.log Y
              ≤ 71 / 135 := by
            rw [div_mul_eq_mul_div, ← add_div, div_le_iff₀ hlogY]
            nlinarith [h1]
          linarith
        have hle : Real.log (q : ℝ) / Real.log Y ≤ μ := by
          rw [hμdef]
          exact le_min hyx.le hycap
        apply Nat.le_floor
        calc (q : ℝ) = Y ^ (Real.log (q : ℝ) / Real.log Y) := by
              rw [Real.rpow_def_of_pos hY0, mul_div_cancel₀ _ hlogY.ne', Real.exp_log hqpos]
          _ ≤ Y ^ μ := Real.rpow_le_rpow_of_exponent_le hY.le hle
  -- the weight at the possibly added integer is nonpositive
  have hq0 : (1 / ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ))
      * Real.log (Real.log (⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℝ) / Real.log Y / (16 / 135)) ≤ 0 := by
    have h1 : (1 : ℝ) ≤ Y ^ (16 / 135 : ℝ) := Real.one_le_rpow hY.le (by norm_num)
    have h2 : 1 ≤ ⌊Y ^ (16 / 135 : ℝ)⌋₊ :=
      Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ Y ^ (16 / 135 : ℝ) by push_cast; linarith)
    have hfl : (0 : ℝ) < ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) := by
      have h3 : (1 : ℝ) ≤ ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast h2
      linarith
    have harg : Real.log (⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℝ) / Real.log Y / (16 / 135) ≤ 1 := by
      rw [div_le_one (by norm_num), div_le_iff₀ hlogY]
      calc Real.log (⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℝ) ≤ Real.log (Y ^ (16 / 135 : ℝ)) :=
            Real.log_le_log (by positivity) (Nat.floor_le (by positivity))
        _ = (16 / 135) * Real.log Y := Real.log_rpow hY0 _
    have hlogarg : Real.log (Real.log (⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℝ) / Real.log Y / (16 / 135)) ≤ 0 :=
      Real.log_nonpos (by positivity) harg
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hlogarg
  -- nonnegativity on the window
  have hposW : ∀ q ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ μ⌋₊).filter Nat.Prime,
      0 ≤ (1 / (q : ℝ)) * Real.log (Real.log (q : ℝ) / Real.log Y / (16 / 135)) := by
    intro q hq
    obtain ⟨hqmem, hqp⟩ := Finset.mem_filter.mp hq
    rw [Finset.mem_Ioc] at hqmem
    have hqpos : (0 : ℝ) < (q : ℝ) := by
      have h : (0 : ℕ) < q := by omega
      exact_mod_cast h
    apply mul_nonneg (by positivity)
    apply Real.log_nonneg
    rw [le_div_iff₀ ha]
    have h2 : Y ^ (16 / 135 : ℝ) < (q : ℝ) := by
      have h3 : (⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℝ) + 1 ≤ (q : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hqmem.1
      have h4 := Nat.lt_floor_add_one (Y ^ (16 / 135 : ℝ))
      linarith
    have h5 := Real.log_le_log (by positivity) h2.le
    rw [Real.log_rpow hY0] at h5
    rw [le_div_iff₀ hlogY] at ⊢
    linarith
  have hmain := sum_le_of_subset_insert hsub hq0 hposW
  have hinner := inner_q_sum_le (Y := Y) (K := K) (μ := μ) hY hK hμ1 hμ2 hbig hne
  linarith [hmain, hinner]



/-- C10: the per-outer-prime bound on the **whole** `q`-range `Y^a ≤ q < p`
(no branch restriction), i.e. `inner_q_sum_le` at `μ = log p / log Y`. -/
private theorem inner_q_full_le {Y : ℝ} {n p : ℕ} {K : ℕ} {μ : ℝ} (hY : 1 < Y) (hK : 0 < K)
    (hp : p.Prime)
    (hμdef : μ = Real.log (p : ℝ) / Real.log Y)
    (hμ1 : 16 / 135 ≤ μ) (hμ2 : μ ≤ 89 / 462 - 0.00000001)
    (hbig : 2 * Real.log 2 ≤ (16 / 135) * Real.log Y)
    (hne : ∀ i : ℕ, i < K →
      ⌈Y ^ (16 / 135 + (i : ℝ) * ((μ - 16 / 135) / (K : ℝ)))⌉₊
        ≤ ⌊Y ^ (16 / 135 + ((i : ℝ) + 1) * ((μ - 16 / 135) / (K : ℝ)))⌋₊) :
    (∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
        Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)),
        (1 / (q : ℝ)) * Real.log (Real.log (q : ℝ) / Real.log Y / (16 / 135)))
      ≤ (1 / 2) * Real.log (μ / (16 / 135)) ^ 2
        + Real.log (μ / (16 / 135))
            * ((μ - 16 / 135) / ((16 / 135) * (K : ℝ))
                + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y))) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have ha : (0 : ℝ) < 16 / 135 := by norm_num
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  -- `⌊Y^μ⌋ = p`
  have hYμ : Y ^ μ = (p : ℝ) := by
    rw [hμdef, Real.rpow_def_of_pos hY0, mul_div_cancel₀ _ hlogY.ne', Real.exp_log hp0]
  have hflμ : ⌊Y ^ μ⌋₊ = p := by rw [hYμ, Nat.floor_natCast]
  -- containment into `insert ⌊Y^a⌋ (window)`
  have hsub : (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
        Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ))
      ⊆ insert ⌊Y ^ (16 / 135 : ℝ)⌋₊
          ((Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ μ⌋₊).filter Nat.Prime) := by
    intro q hq
    obtain ⟨-, hqp, hαq, hqlt⟩ := Finset.mem_filter.mp hq
    have hqpos : (0 : ℝ) < (q : ℝ) := by
      have h : (0 : ℕ) < q := lt_of_lt_of_le (by norm_num) hqp.two_le
      exact_mod_cast h
    rw [Finset.mem_insert]
    by_cases h : q = ⌊Y ^ (16 / 135 : ℝ)⌋₊
    · exact Or.inl h
    · refine Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hqp⟩)
      · have h1 : ⌊Y ^ (16 / 135 : ℝ)⌋₊ ≤ ⌊(q : ℝ)⌋₊ := Nat.floor_mono hαq
        rw [Nat.floor_natCast] at h1
        omega
      · rw [hflμ]
        have h1 : q < p := by exact_mod_cast hqlt
        omega
  -- the weight at the possibly added integer is nonpositive
  have hq0 : (1 / ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ))
      * Real.log (Real.log (⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℝ) / Real.log Y / (16 / 135)) ≤ 0 := by
    have h1 : (1 : ℝ) ≤ Y ^ (16 / 135 : ℝ) := Real.one_le_rpow hY.le (by norm_num)
    have h2 : 1 ≤ ⌊Y ^ (16 / 135 : ℝ)⌋₊ :=
      Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ Y ^ (16 / 135 : ℝ) by push_cast; linarith)
    have hfl : (0 : ℝ) < ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) := by
      have h3 : (1 : ℝ) ≤ ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast h2
      linarith
    have harg : Real.log (⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℝ) / Real.log Y / (16 / 135) ≤ 1 := by
      rw [div_le_one (by norm_num), div_le_iff₀ hlogY]
      calc Real.log (⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℝ) ≤ Real.log (Y ^ (16 / 135 : ℝ)) :=
            Real.log_le_log (by positivity) (Nat.floor_le (by positivity))
        _ = (16 / 135) * Real.log Y := Real.log_rpow hY0 _
    have hlogarg : Real.log (Real.log (⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℝ) / Real.log Y / (16 / 135)) ≤ 0 :=
      Real.log_nonpos (by positivity) harg
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hlogarg
  -- nonnegativity on the window
  have hposW : ∀ q ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ μ⌋₊).filter Nat.Prime,
      0 ≤ (1 / (q : ℝ)) * Real.log (Real.log (q : ℝ) / Real.log Y / (16 / 135)) := by
    intro q hq
    obtain ⟨hqmem, hqp⟩ := Finset.mem_filter.mp hq
    rw [Finset.mem_Ioc] at hqmem
    have hqpos : (0 : ℝ) < (q : ℝ) := by
      have h : (0 : ℕ) < q := by omega
      exact_mod_cast h
    apply mul_nonneg (by positivity)
    apply Real.log_nonneg
    rw [le_div_iff₀ ha]
    have h2 : Y ^ (16 / 135 : ℝ) < (q : ℝ) := by
      have h3 : (⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℝ) + 1 ≤ (q : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hqmem.1
      have h4 := Nat.lt_floor_add_one (Y ^ (16 / 135 : ℝ))
      linarith
    have h5 := Real.log_le_log (by positivity) h2.le
    rw [Real.log_rpow hY0] at h5
    rw [le_div_iff₀ hlogY] at ⊢
    linarith
  have hmain := sum_le_of_subset_insert hsub hq0 hposW
  have hinner := inner_q_sum_le (Y := Y) (K := K) (μ := μ) hY hK hμ1 hμ2 hbig hne
  linarith [hmain, hinner]


-- bricks of pass 20261116T2114Z (verified: results/wip578d/Step2.lean, EXIT=0);
-- the 1759Z bricks above sit in a *relative* namespace, so open it by its resolved name
open LeanLab.Languasco2004.Decomp578d.WIP.LeanLab.Languasco2004.Decomp578d

/-- One mesh step `u → u + w` straddles an integer once `Y^u (Y^w - 1) ≥ 2`. -/
private theorem mesh_step {Y : ℝ} (hY : 1 < Y) {u w : ℝ} (hu : 0 < Y ^ u)
    (hstep : 2 ≤ Y ^ u * (Y ^ w - 1)) :
    ⌈Y ^ u⌉₊ ≤ ⌊Y ^ (u + w)⌋₊ := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hpow : Y ^ (u + w) = Y ^ u * Y ^ w := Real.rpow_add hY0 u w
  have hceil : ((⌈Y ^ u⌉₊ : ℕ) : ℝ) < Y ^ u + 1 := Nat.ceil_lt_add_one hu.le
  have hfloor : Y ^ u * Y ^ w - 1 < ((⌊Y ^ (u + w)⌋₊ : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one (Y ^ (u + w))
    have heq : Y ^ u * Y ^ w = Y ^ (u + w) := hpow.symm
    linarith
  have hstep2 : 2 ≤ Y ^ u * Y ^ w - Y ^ u := by
    have h : Y ^ u * (Y ^ w - 1) = Y ^ u * Y ^ w - Y ^ u := by ring
    linarith
  have hkey : ((⌈Y ^ u⌉₊ : ℕ) : ℝ) < ((⌊Y ^ (u + w)⌋₊ : ℕ) : ℝ) := by linarith
  exact le_of_lt (Nat.cast_lt.mp hkey)

/-- The blocks of the `K`-mesh with step `W` on `[a, a + K W]` all straddle an integer, uniformly,
from the single coarse step hypothesis `2 ≤ Y^a (Y^{w0} - 1)` with `w0 ≤ W`. -/
private theorem mesh_cond {Y : ℝ} (hY : 1 < Y) {a W w0 : ℝ}
    (hW : 0 ≤ W) (hw0 : 0 ≤ w0) (hw0W : w0 ≤ W)
    (hstep : 2 ≤ Y ^ a * (Y ^ w0 - 1)) (i : ℕ) :
    ⌈Y ^ (a + (i : ℝ) * W)⌉₊ ≤ ⌊Y ^ (a + ((i : ℝ) + 1) * W)⌋₊ := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hY1 : (1 : ℝ) ≤ Y := hY.le
  have hiW : (0 : ℝ) ≤ (i : ℝ) * W := by positivity
  have hbase : Y ^ a ≤ Y ^ (a + (i : ℝ) * W) :=
    Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
  have hstepW : Y ^ w0 - 1 ≤ Y ^ W - 1 := by
    have h1 : Y ^ w0 ≤ Y ^ W := Real.rpow_le_rpow_of_exponent_le hY1 hw0W
    linarith
  have hnn : (0 : ℝ) ≤ Y ^ w0 - 1 := by
    have h1 : (1 : ℝ) ≤ Y ^ w0 := Real.one_le_rpow hY1 hw0
    linarith
  have hprod : Y ^ a * (Y ^ w0 - 1) ≤ Y ^ (a + (i : ℝ) * W) * (Y ^ W - 1) :=
    mul_le_mul hbase hstepW hnn (le_of_lt (Real.rpow_pos_of_pos hY0 _))
  have hstep' : 2 ≤ Y ^ (a + (i : ℝ) * W) * (Y ^ W - 1) := le_trans hstep hprod
  have hu : 0 < Y ^ (a + (i : ℝ) * W) := Real.rpow_pos_of_pos hY0 _
  have hmain := mesh_step hY hu hstep'
  rwa [show a + (i : ℝ) * W + W = a + ((i : ℝ) + 1) * W by ring] at hmain

/-- The `pairDomain` sum splits over the outer prime: dropping every `pairDomain` constraint
except `Y^(16/135) < p ≤ Y^(89/462-ε)`, `Y^(16/135) ≤ q < p` and `q ≤ n` only enlarges it. -/
private theorem pair_sum_split_le {Y : ℝ} (hY : 1 < Y) (n : ℕ) :
    (∑ pq ∈ Source565.pairDomain true Y n,
        (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
          * Real.log (Real.log (pq.2 : ℝ) / ((16 / 135) * Real.log Y)))
      ≤ ∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ) *
            (∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
                Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)),
              (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y))) := by
  classical
  have hY0 : (0 : ℝ) < Y := by linarith
  set W : Finset ℕ :=
    (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter Nat.Prime with hW
  set T : ℕ → Finset ℕ := fun p =>
    (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
      Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)) with hT
  have hfib : ∀ p : ℕ, (Source565.pairDomain true Y n).filter (fun x => x.1 = p)
      = ((T p).filter (fun q => (p, q) ∈ Source565.pairDomain true Y n)).image (fun q => (p, q)) := by
    intro p
    ext x
    obtain ⟨p', q'⟩ := x
    constructor
    · intro hx
      obtain ⟨hxmem, hx1⟩ := Finset.mem_filter.mp hx
      have hx1' : p' = p := hx1
      subst hx1'
      refine Finset.mem_image.mpr ⟨q', ?_, rfl⟩
      obtain ⟨hmem, hconds⟩ := Finset.mem_filter.mp hxmem
      obtain ⟨hpr, hαp, hsp, hqr, hαq, hqmin, hgrp, hdec, hβp⟩ := hconds
      refine Finset.mem_filter.mpr ⟨?_, hxmem⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by
          have := (Finset.mem_product.mp hmem).2
          simpa using this), hqr, le_of_lt hαq, lt_of_lt_of_le hqmin (min_le_left _ _)⟩
    · intro hx
      obtain ⟨q, hq, hqx⟩ := Finset.mem_image.mp hx
      obtain ⟨hqp, hqq⟩ : p = p' ∧ q = q' := Prod.mk.inj hqx
      subst hqp
      subst hqq
      obtain ⟨-, hqpD⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hqpD, rfl⟩
  have hstep : ∀ p ∈ W, (∑ x ∈ (Source565.pairDomain true Y n).filter (fun x => x.1 = p),
        (1 : ℝ) / ((x.1 : ℝ) * (x.2 : ℝ))
          * Real.log (Real.log (x.2 : ℝ) / ((16 / 135) * Real.log Y)))
      ≤ (1 : ℝ) / (p : ℝ) * (∑ q ∈ T p,
          (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y))) := by
    intro p hp
    rw [hfib p]
    rw [Finset.sum_image (g := fun q => (p, q))
      (f := fun x : ℕ × ℕ => (1 : ℝ) / ((x.1 : ℝ) * (x.2 : ℝ))
        * Real.log (Real.log (x.2 : ℝ) / ((16 / 135) * Real.log Y)))
      (by intro x _ y _ h; exact (Prod.mk.inj h).2)]
    dsimp only
    rw [Finset.mul_sum]
    have hsummand : ∀ q : ℕ, (1 : ℝ) / ((p : ℝ) * (q : ℝ))
        * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y))
        = (1 : ℝ) / (p : ℝ) * ((1 : ℝ) / (q : ℝ)
            * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y))) := by
      intro q
      field_simp
    simp only [hsummand]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro q hq
      exact (Finset.mem_filter.mp hq).1
    · intro q hq _
      have hqa : Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) := (Finset.mem_filter.mp hq).2.2.1
      have hqa0 : (0 : ℝ) < Y ^ (16 / 135 : ℝ) := Real.rpow_pos_of_pos hY0 _
      have hlogq : Real.log (Y ^ (16 / 135 : ℝ)) ≤ Real.log (q : ℝ) :=
        Real.log_le_log hqa0 hqa
      rw [Real.log_rpow hY0] at hlogq
      have hden : (0 : ℝ) < (16 / 135) * Real.log Y := by
        have h1 : (0 : ℝ) < Real.log Y := Real.log_pos hY
        have h2 : (0 : ℝ) < 16 / 135 := by norm_num
        positivity
      have hratio : (1 : ℝ) ≤ Real.log (q : ℝ) / ((16 / 135) * Real.log Y) := by
        rw [le_div_iff₀ hden]
        linarith
      have hlog0 : 0 ≤ Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y)) :=
        Real.log_nonneg hratio
      have hp0 : (0 : ℝ) < (p : ℝ) := by
        have := (Finset.mem_filter.mp hp).2
        exact_mod_cast this.pos
      have hq0 : (0 : ℝ) < (q : ℝ) := by
        have := (Finset.mem_filter.mp hq).2.1
        exact_mod_cast this.pos
      exact mul_nonneg (by positivity) (mul_nonneg (by positivity) hlog0)
  have hmaps : ∀ x ∈ Source565.pairDomain true Y n, x.1 ∈ W := by
    intro x hx
    obtain ⟨p, q⟩ := x
    obtain ⟨hmem, hconds⟩ := Finset.mem_filter.mp hx
    obtain ⟨hpr, hαp, hsp, hqr, hαq, hqmin, hgrp, hdec, hβp⟩ := hconds
    rw [hW, Finset.mem_filter]
    refine ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hpr⟩
    · have h1 : ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) ≤ Y ^ (16 / 135 : ℝ) :=
        Nat.floor_le (le_of_lt (Real.rpow_pos_of_pos hY0 _))
      have h2 : ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) < (p : ℝ) := lt_of_le_of_lt h1 hαp
      exact Nat.cast_lt.mp h2
    · exact Nat.le_floor (hβp rfl)
  calc (∑ pq ∈ Source565.pairDomain true Y n,
        (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
          * Real.log (Real.log (pq.2 : ℝ) / ((16 / 135) * Real.log Y)))
      = ∑ p ∈ W, ∑ x ∈ (Source565.pairDomain true Y n).filter (fun x => x.1 = p),
          (1 : ℝ) / ((x.1 : ℝ) * (x.2 : ℝ))
            * Real.log (Real.log (x.2 : ℝ) / ((16 / 135) * Real.log Y)) :=
        (Finset.sum_fiberwise_of_maps_to (t := W) hmaps
          (fun x : ℕ × ℕ => (1 : ℝ) / ((x.1 : ℝ) * (x.2 : ℝ))
            * Real.log (Real.log (x.2 : ℝ) / ((16 / 135) * Real.log Y)))).symm
    _ ≤ ∑ p ∈ W, (1 : ℝ) / (p : ℝ) * (∑ q ∈ T p,
          (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y))) :=
        Finset.sum_le_sum hstep
    _ = ∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ) * (∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
              Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)),
            (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y))) := by
        rw [hW, hT]

/-- The outer staircase at `φ x = ½ log(x/a)² + e·log(x/a)` over the outer prime window: the
weighted prime sum is at most its integral plus `φ b · e`.  The mesh-plus-Mertens error
`e = (b-a)/(aK) + K·42 log 2/(a log Y)` is kept symbolic so a chooser can send it to `0`. -/
private theorem outer_full_le {Y : ℝ} {K : ℕ} {e : ℝ} (hY : 1 < Y) (hK2 : 2 ≤ K)
    (hbig : 2 * Real.log 2 ≤ (16 / 135) * Real.log Y)
    (he : e = (89 / 462 - 0.00000001 - 16 / 135) / ((16 / 135) * (K : ℝ))
            + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)))
    (hstep : 2 ≤ Y ^ (16 / 135 : ℝ) *
      (Y ^ ((89 / 462 - 0.00000001 - 16 / 135) / ((K : ℝ) ^ 2)) - 1)) :
    (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ) *
          ((1 / 2) * Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) ^ 2
            + Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) * e))
      ≤ Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 3 / 6
        + e * (Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 2
            + Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) * e) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have ha : (0 : ℝ) < 16 / 135 := by norm_num
  have hab : (16 / 135 : ℝ) ≤ 89 / 462 - 0.00000001 := by norm_num
  have hd : (0 : ℝ) < 89 / 462 - 0.00000001 - 16 / 135 := by norm_num
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hKerr : (0 : ℝ) ≤ 42 * Real.log 2 / ((16 / 135) * Real.log Y) := by
    have h1 : (0 : ℝ) < Real.log Y := hlogY
    have h2 : (0 : ℝ) < 16 / 135 := by norm_num
    positivity
  have he0 : 0 ≤ e := by rw [he]; positivity
  have hW0 : (0 : ℝ) ≤ (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ) :=
    div_nonneg (le_of_lt hd) (le_of_lt hKpos)
  have hw00 : (0 : ℝ) ≤ (89 / 462 - 0.00000001 - 16 / 135) / ((K : ℝ) ^ 2) :=
    div_nonneg (le_of_lt hd) (by positivity)
  have hw0W : (89 / 462 - 0.00000001 - 16 / 135) / ((K : ℝ) ^ 2)
      ≤ (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hKpos]
    have hK2' : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK2
    nlinarith [hd, hKpos, hK2']
  have hne : ∀ i : ℕ, i < K →
      ⌈Y ^ (16 / 135 + (i : ℝ) * ((89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)))⌉₊
        ≤ ⌊Y ^ (16 / 135 + ((i : ℝ) + 1) * ((89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)))⌋₊ := by
    intro i _
    exact mesh_cond (a := 16 / 135) (W := (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ))
      (w0 := (89 / 462 - 0.00000001 - 16 / 135) / ((K : ℝ) ^ 2)) hY hW0 hw00 hw0W hstep i
  set Phi : ℝ → ℝ := fun x => (1 / 2) * Real.log (x / (16 / 135)) ^ 2
    + Real.log (x / (16 / 135)) * e with hPhi
  have hmono : ∀ x y : ℝ, 16 / 135 ≤ x → x ≤ y → y ≤ 89 / 462 - 0.00000001 → Phi x ≤ Phi y := by
    intro x y hx hxy hy
    have hL : Real.log (x / (16 / 135)) ≤ Real.log (y / (16 / 135)) :=
      Real.log_le_log (by positivity) (by gcongr)
    have hL0 : 0 ≤ Real.log (x / (16 / 135)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ ha]
      linarith
    have hsq : Real.log (x / (16 / 135)) ^ 2 ≤ Real.log (y / (16 / 135)) ^ 2 :=
      pow_le_pow_left₀ hL0 hL 2
    simp only [hPhi]
    have h1 : Real.log (x / (16 / 135)) * e ≤ Real.log (y / (16 / 135)) * e :=
      mul_le_mul_of_nonneg_right hL he0
    linarith
  have hnn : ∀ x : ℝ, 16 / 135 ≤ x → x ≤ 89 / 462 - 0.00000001 → 0 ≤ Phi x := by
    intro x hx _
    have hL : 0 ≤ Real.log (x / (16 / 135)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ ha]
      linarith
    simp only [hPhi]
    have h1 : 0 ≤ Real.log (x / (16 / 135)) * e := mul_nonneg hL he0
    nlinarith [sq_nonneg (Real.log (x / (16 / 135)))]
  have hlogcont : ContinuousOn (fun x : ℝ => Real.log (x / (16 / 135))) (Set.Icc (16 / 135) (89 / 462 - 0.00000001)) := by
    refine ContinuousOn.log (by fun_prop) ?_
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha hx.1
    exact div_ne_zero hx0.ne' (by norm_num)
  have hint : ∀ u v : ℝ, 16 / 135 ≤ u → u ≤ v → v ≤ 89 / 462 - 0.00000001 →
      IntervalIntegrable (fun x : ℝ => Phi x / x) MeasureTheory.volume u v := by
    intro u v hu huv hv
    apply ContinuousOn.intervalIntegrable_of_Icc huv
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le ha hu
    have hsub : Set.Icc u v ⊆ Set.Icc (16 / 135) (89 / 462 - 0.00000001) :=
      Set.Icc_subset_Icc hu hv
    have hcont : ContinuousOn (fun x : ℝ => Phi x) (Set.Icc u v) := by
      simp only [hPhi]
      exact ((continuousOn_const.mul ((hlogcont.mono hsub).pow 2)).add
        ((hlogcont.mono hsub).mul continuousOn_const))
    exact hcont.div continuousOn_id (fun x hx => (lt_of_lt_of_le hu0 hx.1).ne')
  have hmain := prime_sum_block_le (Y := Y) (K := K) (μ := 89 / 462 - 0.00000001) hY
    (by omega) hab le_rfl hbig Phi hmono hnn hint hne
  rw [← he] at hmain
  -- evaluate the integral of `Phi x / x`
  have hI1 : IntervalIntegrable (fun x : ℝ => (1 / 2) * (Real.log (x / (16 / 135)) ^ 2 / x))
      MeasureTheory.volume (16 / 135) (89 / 462 - 0.00000001) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    refine ContinuousOn.mul continuousOn_const ?_
    refine hlogcont.pow 2 |>.div continuousOn_id ?_
    intro x hx
    exact (lt_of_lt_of_le ha hx.1).ne'
  have hI2 : IntervalIntegrable (fun x : ℝ => Real.log (x / (16 / 135)) / x)
      MeasureTheory.volume (16 / 135) (89 / 462 - 0.00000001) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    refine hlogcont.div continuousOn_id ?_
    intro x hx
    exact (lt_of_lt_of_le ha hx.1).ne'
  have hI1e : (∫ x in (16 / 135)..(89 / 462 - 0.00000001),
      (1 / 2) * (Real.log (x / (16 / 135)) ^ 2 / x))
      = Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 3 / 6 := by
    rw [intervalIntegral.integral_const_mul,
      integral_logsq_ratio (16 / 135) (89 / 462 - 0.00000001) ha hab]
    ring
  have hI2e : (∫ x in (16 / 135)..(89 / 462 - 0.00000001),
      Real.log (x / (16 / 135)) / x)
      = Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 2 / 2 :=
    Integral565.integral_log_ratio (16 / 135) (89 / 462 - 0.00000001) ha hab
  have hPhiInt : (∫ x in (16 / 135)..(89 / 462 - 0.00000001), Phi x / x)
      = Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 3 / 6
        + e * (Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 2 / 2) := by
    have hEq : (∫ x in (16 / 135)..(89 / 462 - 0.00000001), Phi x / x)
        = ∫ x in (16 / 135)..(89 / 462 - 0.00000001),
            ((1 / 2) * (Real.log (x / (16 / 135)) ^ 2 / x)
              + e * (Real.log (x / (16 / 135)) / x)) := by
      apply intervalIntegral.integral_congr
      intro x _
      simp only [hPhi]
      field_simp
      try ring
    rw [hEq, intervalIntegral.integral_add hI1 (hI2.const_mul e),
      hI1e, intervalIntegral.integral_const_mul, hI2e]
  have hPhiB : Phi (89 / 462 - 0.00000001)
      = (1 / 2) * Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 2
        + Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) * e := by
    simp only [hPhi]
  rw [hPhiInt, hPhiB] at hmain
  set L : ℝ := Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) with hLdef
  have key : (L ^ 3 / 6 + e * (L ^ 2 / 2)) + (1 / 2 * L ^ 2 + L * e) * e
      = L ^ 3 / 6 + e * (L ^ 2 + L * e) := by ring
  exact le_trans hmain (le_of_eq key)


/-- The two ways the model's weight is written (`log q / (a log Y)` versus `log q / log Y / a`)
agree, which is what lets the `inner_q_*` bricks be applied to the model's inner sum. -/
private theorem log_arg_div {x Y : ℝ} (hx : 0 < x) (hY : 0 < Real.log Y) :
    Real.log x / ((16 / 135) * Real.log Y) = Real.log x / Real.log Y / (16 / 135) := by
  have h1 : (0 : ℝ) < 16 / 135 := by norm_num
  field_simp

/-- The inner `q`-sum at a fixed outer prime `p` past the first mesh block: `inner_q_full_le` at
`μ = log p/log Y`, whose mesh is coarse enough because `x_p ≥ a + (b-a)/K`. -/
private theorem inner_le_psi_big {Y : ℝ} {n p K : ℕ} {e : ℝ} (hY : 1 < Y) (hK2 : 2 ≤ K)
    (hbig : 2 * Real.log 2 ≤ (16 / 135) * Real.log Y)
    (he : e = (89 / 462 - 0.00000001 - 16 / 135) / ((16 / 135) * (K : ℝ))
            + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)))
    (hstep : 2 ≤ Y ^ (16 / 135 : ℝ) *
      (Y ^ ((89 / 462 - 0.00000001 - 16 / 135) / ((K : ℝ) ^ 2)) - 1))
    (hp : p.Prime) (hpa : Y ^ (16 / 135 : ℝ) < (p : ℝ))
    (hpb : (p : ℝ) ≤ Y ^ (89 / 462 - 0.00000001 : ℝ))
    (hlarge : Y ^ ((16 / 135 : ℝ) + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)) < (p : ℝ)) :
    (∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
        Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)),
        (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y)))
      ≤ (1 / 2) * Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) ^ 2
        + Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) * e := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have ha : (0 : ℝ) < 16 / 135 := by norm_num
  have hd : (0 : ℝ) < 89 / 462 - 0.00000001 - 16 / 135 := by norm_num
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hxp_gt : 16 / 135 < Real.log (p : ℝ) / Real.log Y := by
    have h1 : Real.log (Y ^ (16 / 135 : ℝ)) < Real.log (p : ℝ) :=
      Real.log_lt_log (Real.rpow_pos_of_pos hY0 _) hpa
    rw [Real.log_rpow hY0] at h1
    rw [lt_div_iff₀ hlogY]
    linarith
  have hxp_le : Real.log (p : ℝ) / Real.log Y ≤ 89 / 462 - 0.00000001 := by
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    have h1 : Real.log (p : ℝ) ≤ Real.log (Y ^ (89 / 462 - 0.00000001 : ℝ)) :=
      Real.log_le_log hp0 hpb
    rw [Real.log_rpow hY0] at h1
    rw [div_le_iff₀ hlogY]
    linarith
  have hc1 : 16 / 135 + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)
      ≤ Real.log (p : ℝ) / Real.log Y := by
    have h2 : Real.log (Y ^ ((16 / 135 : ℝ) + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)))
        < Real.log (p : ℝ) := Real.log_lt_log (Real.rpow_pos_of_pos hY0 _) hlarge
    rw [Real.log_rpow hY0] at h2
    rw [le_div_iff₀ hlogY]
    linarith
  have hW0 : (0 : ℝ) ≤ (Real.log (p : ℝ) / Real.log Y - 16 / 135) / (K : ℝ) :=
    div_nonneg (by linarith) (le_of_lt hKpos)
  have hw00 : (0 : ℝ) ≤ (89 / 462 - 0.00000001 - 16 / 135) / ((K : ℝ) ^ 2) :=
    div_nonneg (le_of_lt hd) (by positivity)
  have hw0W : (89 / 462 - 0.00000001 - 16 / 135) / ((K : ℝ) ^ 2)
      ≤ (Real.log (p : ℝ) / Real.log Y - 16 / 135) / (K : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hKpos]
    have hK2' : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK2
    have hs : (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)
        ≤ Real.log (p : ℝ) / Real.log Y - 16 / 135 := by linarith
    have hs' : (89 / 462 - 0.00000001 - 16 / 135)
        ≤ (Real.log (p : ℝ) / Real.log Y - 16 / 135) * (K : ℝ) := by
      rw [div_le_iff₀ hKpos] at hs
      linarith
    nlinarith [hs', hd, hKpos, hK2']
  have hne : ∀ i : ℕ, i < K →
      ⌈Y ^ (16 / 135 + (i : ℝ) * ((Real.log (p : ℝ) / Real.log Y - 16 / 135) / (K : ℝ)))⌉₊
        ≤ ⌊Y ^ (16 / 135 + ((i : ℝ) + 1)
            * ((Real.log (p : ℝ) / Real.log Y - 16 / 135) / (K : ℝ)))⌋₊ := by
    intro i _
    exact mesh_cond (a := 16 / 135) (W := (Real.log (p : ℝ) / Real.log Y - 16 / 135) / (K : ℝ))
      (w0 := (89 / 462 - 0.00000001 - 16 / 135) / ((K : ℝ) ^ 2)) hY hW0 hw00 hw0W hstep i
  have hconv : (∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
        Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)),
        (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y)))
      = (∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
        Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)),
        (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / Real.log Y / (16 / 135))) := by
    refine Finset.sum_congr rfl (fun q hq => ?_)
    have hq0 : (0 : ℝ) < (q : ℝ) := by
      have := (Finset.mem_filter.mp hq).2.1
      exact_mod_cast this.pos
    rw [log_arg_div hq0 hlogY]
  rw [hconv]
  have hmain := inner_q_full_le (Y := Y) (n := n) (p := p) (K := K)
    (μ := Real.log (p : ℝ) / Real.log Y) hY (by omega) hp rfl (le_of_lt hxp_gt) hxp_le hbig hne
  have hmesh : (Real.log (p : ℝ) / Real.log Y - 16 / 135) / ((16 / 135) * (K : ℝ))
      + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)) ≤ e := by
    rw [he]
    have h1 : (Real.log (p : ℝ) / Real.log Y - 16 / 135) / ((16 / 135) * (K : ℝ))
        ≤ (89 / 462 - 0.00000001 - 16 / 135) / ((16 / 135) * (K : ℝ)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    linarith
  have hL : 0 ≤ Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ ha]
    linarith
  have hthis : Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135))
      * ((Real.log (p : ℝ) / Real.log Y - 16 / 135) / ((16 / 135) * (K : ℝ))
        + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)))
      ≤ Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) * e :=
    mul_le_mul_of_nonneg_left hmesh hL
  linarith [hmain, hthis]

/-- The inner `q`-sum at a fixed outer prime `p` in the **first** mesh block
(`p ≤ Y^(a + (b-a)/K)`): the window is short, so the crude `3e²` suffices. -/
private theorem inner_le_psi_small {Y : ℝ} {n p K : ℕ} {e : ℝ} (hY : 1 < Y) (hK2 : 2 ≤ K)
    (hbig : 2 * Real.log 2 ≤ (16 / 135) * Real.log Y)
    (he : e = (89 / 462 - 0.00000001 - 16 / 135) / ((16 / 135) * (K : ℝ))
            + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)))
    (hstep : 2 ≤ Y ^ (16 / 135 : ℝ) *
      (Y ^ ((89 / 462 - 0.00000001 - 16 / 135) / ((K : ℝ) ^ 2)) - 1))
    (hp : p.Prime) (hpa : Y ^ (16 / 135 : ℝ) < (p : ℝ))
    (hpb : (p : ℝ) ≤ Y ^ (89 / 462 - 0.00000001 : ℝ))
    (hsmall : (p : ℝ) ≤ Y ^ ((16 / 135 : ℝ) + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ))) :
    (∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
        Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)),
        (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y)))
      ≤ 3 * e ^ 2 := by
  classical
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have ha : (0 : ℝ) < 16 / 135 := by norm_num
  have hd : (0 : ℝ) < 89 / 462 - 0.00000001 - 16 / 135 := by norm_num
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hK2' : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK2
  have he0 : 0 ≤ e := by rw [he]; positivity
  have hw00 : (0 : ℝ) ≤ (89 / 462 - 0.00000001 - 16 / 135) / ((K : ℝ) ^ 2) :=
    div_nonneg (le_of_lt hd) (by positivity)
  -- containment in the first mesh block
  have hsub : ((range (n + 1)).filter (fun q : ℕ => q.Prime ∧
      Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)))
      ⊆ insert ⌊Y ^ (16 / 135 : ℝ)⌋₊
          ((Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊
            ⌊Y ^ ((16 / 135 : ℝ) + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ))⌋₊).filter
              Nat.Prime) := by
    intro q hq
    obtain ⟨-, hqr, hqa, hqp⟩ := Finset.mem_filter.mp hq
    have hqlt : (q : ℝ) ≤ Y ^ ((16 / 135 : ℝ) + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)) :=
      le_trans (le_of_lt hqp) hsmall
    by_cases h0 : q = ⌊Y ^ (16 / 135 : ℝ)⌋₊
    · exact Finset.mem_insert.mpr (Or.inl h0)
    · refine Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hqr⟩))
      · have h1 : ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) ≤ Y ^ (16 / 135 : ℝ) :=
          Nat.floor_le (le_of_lt (Real.rpow_pos_of_pos hY0 _))
        have h2 : ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) ≤ (q : ℝ) := le_trans h1 hqa
        rcases lt_or_eq_of_le h2 with h3 | h3
        · exact Nat.cast_lt.mp h3
        · exact absurd (by exact_mod_cast h3.symm) h0
      · exact Nat.le_floor hqlt
  -- at `⌊Y^a⌋` the weight vanishes
  have hq0le : (1 : ℝ) / ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ)
      * Real.log (Real.log ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ)
        / ((16 / 135) * Real.log Y)) ≤ 0 := by
    have hq01 : (1 : ℝ) ≤ ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) := by
      have h1 : (1 : ℝ) ≤ Y ^ (16 / 135 : ℝ) := Real.one_le_rpow hY.le (by norm_num)
      have h2 : (1 : ℕ) ≤ ⌊Y ^ (16 / 135 : ℝ)⌋₊ := Nat.le_floor (by simpa using h1)
      exact_mod_cast h2
    have hq0log : Real.log (Real.log ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ)
        / ((16 / 135) * Real.log Y)) ≤ 0 := by
      apply Real.log_nonpos
      · apply div_nonneg _ (le_of_lt (by positivity : (0 : ℝ) < (16 / 135) * Real.log Y))
        exact Real.log_nonneg hq01
      · rw [div_le_one (by positivity)]
        have h1 : ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) ≤ Y ^ (16 / 135 : ℝ) :=
          Nat.floor_le (le_of_lt (Real.rpow_pos_of_pos hY0 _))
        have h2 : Real.log ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) ≤ Real.log (Y ^ (16 / 135 : ℝ)) :=
          Real.log_le_log (by positivity) h1
        rw [Real.log_rpow hY0] at h2
        exact h2
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hq0log
  have hstep1 := sum_le_of_subset_insert
    (s := (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
      Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)))
    (t := (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊
      ⌊Y ^ ((16 / 135 : ℝ) + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ))⌋₊).filter Nat.Prime)
    (q0 := ⌊Y ^ (16 / 135 : ℝ)⌋₊)
    (f := fun q : ℕ => (1 : ℝ) / (q : ℝ)
      * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y)))
    hsub hq0le (by
      intro x hx
      have hlt : ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) < (x : ℝ) := by
        have h1 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hx).1).1
        exact_mod_cast h1
      have h3 : Y ^ (16 / 135 : ℝ) < ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have h4 : ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) + 1 ≤ (x : ℝ) := by
        have h5 : ⌊Y ^ (16 / 135 : ℝ)⌋₊ + 1 ≤ x :=
          (Finset.mem_Ioc.mp (Finset.mem_filter.mp hx).1).1
        exact_mod_cast h5
      have hxa : Y ^ (16 / 135 : ℝ) ≤ (x : ℝ) := le_of_lt (lt_of_lt_of_le h3 h4)
      have hx0 : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hY0 _) hxa
      have hlogx : Real.log (Y ^ (16 / 135 : ℝ)) ≤ Real.log (x : ℝ) :=
        Real.log_le_log (Real.rpow_pos_of_pos hY0 _) hxa
      rw [Real.log_rpow hY0] at hlogx
      have hden : (0 : ℝ) < (16 / 135) * Real.log Y := by positivity
      have hratio : (1 : ℝ) ≤ Real.log (x : ℝ) / ((16 / 135) * Real.log Y) := by
        rw [le_div_iff₀ hden]
        linarith
      exact mul_nonneg (by positivity) (Real.log_nonneg hratio))
  -- the first block's own mesh and `inner_q_sum_le` at `μ = c₁`
  have hstep_eq : (16 / 135 + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ) - 16 / 135)
      / (K : ℝ) = (89 / 462 - 0.00000001 - 16 / 135) / ((K : ℝ) ^ 2) := by
    field_simp
    ring
  have hne1 : ∀ i : ℕ, i < K →
      ⌈Y ^ (16 / 135 + (i : ℝ) * ((16 / 135 + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)
          - 16 / 135) / (K : ℝ)))⌉₊
        ≤ ⌊Y ^ (16 / 135 + ((i : ℝ) + 1)
            * ((16 / 135 + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ) - 16 / 135)
              / (K : ℝ)))⌋₊ := by
    intro i _
    rw [hstep_eq]
    exact mesh_cond (a := 16 / 135) (W := (89 / 462 - 0.00000001 - 16 / 135) / ((K : ℝ) ^ 2))
      (w0 := (89 / 462 - 0.00000001 - 16 / 135) / ((K : ℝ) ^ 2)) hY hw00 hw00 le_rfl hstep i
  have hc1 : (16 / 135 : ℝ) ≤ 16 / 135 + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ) := by
    have h : (0 : ℝ) ≤ (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ) :=
      div_nonneg (le_of_lt hd) (le_of_lt hKpos)
    linarith
  have hstep2 := inner_q_sum_le (Y := Y) (K := K)
    (μ := 16 / 135 + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)) hY (by omega) hc1 (by
      have h1 : (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)
          ≤ (89 / 462 - 0.00000001 - 16 / 135) := by
        rw [div_le_iff₀ hKpos]
        nlinarith [hd, hK2']
      linarith) hbig hne1
  -- the analytic bounds: `log(c₁/a) ≤ e` and the block error is `≤ e`
  have hlogc1 : Real.log ((16 / 135 + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)) / (16 / 135))
      ≤ (89 / 462 - 0.00000001 - 16 / 135) / ((16 / 135) * (K : ℝ)) := by
    have heq : (16 / 135 + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)) / (16 / 135)
        = 1 + (89 / 462 - 0.00000001 - 16 / 135) / ((16 / 135) * (K : ℝ)) := by
      field_simp
    rw [heq]
    have hpos : (0 : ℝ) < 1 + (89 / 462 - 0.00000001 - 16 / 135) / ((16 / 135) * (K : ℝ)) := by
      have h : (0 : ℝ) ≤ (89 / 462 - 0.00000001 - 16 / 135) / ((16 / 135) * (K : ℝ)) := by positivity
      linarith
    have h := Real.log_le_sub_one_of_pos hpos
    linarith
  have hlogc1e : Real.log ((16 / 135 + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)) / (16 / 135))
      ≤ e := by
    refine le_trans hlogc1 ?_
    rw [he]
    have h1 : (0 : ℝ) ≤ (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)) := by positivity
    linarith
  have hee : (16 / 135 + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ) - 16 / 135)
      / ((16 / 135) * (K : ℝ)) ≤ e := by
    have hcast : (16 / 135 + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ) - 16 / 135)
        / ((16 / 135) * (K : ℝ))
        = (89 / 462 - 0.00000001 - 16 / 135) / ((16 / 135) * ((K : ℝ) ^ 2)) := by
      field_simp
      ring
    rw [hcast, he]
    have h1 : (89 / 462 - 0.00000001 - 16 / 135) / ((16 / 135) * ((K : ℝ) ^ 2))
        ≤ (89 / 462 - 0.00000001 - 16 / 135) / ((16 / 135) * (K : ℝ)) := by
      apply div_le_div_of_nonneg_left (le_of_lt hd) (by positivity)
      nlinarith [hKpos, hK2']
    have h2 : (0 : ℝ) ≤ (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)) := by positivity
    linarith
  have hlogc1nn : 0 ≤ Real.log ((16 / 135 + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ))
      / (16 / 135)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ ha]
    have h : (0 : ℝ) ≤ (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ) :=
      div_nonneg (le_of_lt hd) (le_of_lt hKpos)
    linarith
  have hfin : (1 / 2) * Real.log ((16 / 135 + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ))
        / (16 / 135)) ^ 2
      + Real.log ((16 / 135 + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)) / (16 / 135))
        * ((16 / 135 + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ) - 16 / 135)
            / ((16 / 135) * (K : ℝ))
          + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y))) ≤ 3 * e ^ 2 := by
    nlinarith [hlogc1e, hlogc1nn, he0, sq_nonneg e]
  have hcv : (∑ q ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊
        ⌊Y ^ ((16 / 135 : ℝ) + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ))⌋₊).filter Nat.Prime,
        (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y)))
      = (∑ q ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊
        ⌊Y ^ ((16 / 135 : ℝ) + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ))⌋₊).filter Nat.Prime,
        (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / Real.log Y / (16 / 135))) := by
    refine Finset.sum_congr rfl (fun q hq => ?_)
    have hq0 : (0 : ℝ) < (q : ℝ) := by
      have h1 : ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) < (q : ℝ) := by
        exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).1
      have h2 : (0 : ℝ) ≤ ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) := by positivity
      linarith
    rw [log_arg_div hq0 hlogY]
  rw [← hcv] at hstep2
  linarith [hstep1, hstep2, hfin]

/-- The full branch of the model: the pair sum is at most `log(b/a)³/6 + O(e)`, with the first
mesh block contributing `3e²·S`.  Glues `pair_sum_split_le`, the two inner bounds and
`outer_full_le`. -/
private theorem pair_full_le {Y : ℝ} {n K : ℕ} {e S : ℝ} (hY : 1 < Y) (hK2 : 2 ≤ K)
    (hbig : 2 * Real.log 2 ≤ (16 / 135) * Real.log Y)
    (he : e = (89 / 462 - 0.00000001 - 16 / 135) / ((16 / 135) * (K : ℝ))
            + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)))
    (hstep : 2 ≤ Y ^ (16 / 135 : ℝ) *
      (Y ^ ((89 / 462 - 0.00000001 - 16 / 135) / ((K : ℝ) ^ 2)) - 1))
    (hS : (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
            Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤ S) (hS0 : 0 ≤ S) :
    (∑ pq ∈ Source565.pairDomain true Y n,
        (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
          * Real.log (Real.log (pq.2 : ℝ) / ((16 / 135) * Real.log Y)))
      ≤ Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 3 / 6
        + e * (Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 2
            + Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) * e) + 3 * e ^ 2 * S := by
  classical
  have hY0 : (0 : ℝ) < Y := by linarith
  have ha : (0 : ℝ) < 16 / 135 := by norm_num
  have hd : (0 : ℝ) < 89 / 462 - 0.00000001 - 16 / 135 := by norm_num
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have he0 : 0 ≤ e := by rw [he]; positivity
  have hwin : ∀ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
      Nat.Prime, p.Prime ∧ Y ^ (16 / 135 : ℝ) < (p : ℝ) ∧
        (p : ℝ) ≤ Y ^ (89 / 462 - 0.00000001 : ℝ) := by
    intro p hp
    obtain ⟨hmem, hpr⟩ := Finset.mem_filter.mp hp
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hmem
    refine ⟨hpr, ?_, ?_⟩
    · have h1 : ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) < (p : ℝ) := by exact_mod_cast hlo
      have h2 : Y ^ (16 / 135 : ℝ) < ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have h3 : ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by
        have h4 : ⌊Y ^ (16 / 135 : ℝ)⌋₊ + 1 ≤ p := hlo
        exact_mod_cast h4
      linarith
    · have h1 : ((p : ℕ) : ℝ) ≤ ((⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast hhi
      have h2 : ((⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊ : ℕ) : ℝ)
          ≤ Y ^ (89 / 462 - 0.00000001 : ℝ) :=
        Nat.floor_le (le_of_lt (Real.rpow_pos_of_pos hY0 _))
      linarith
  -- per-prime inner bound
  have hpoint : ∀ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
      Nat.Prime,
      (∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
          Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)),
          (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y)))
        ≤ ((1 / 2) * Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) ^ 2
            + Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) * e)
          + (if (p : ℝ) ≤ Y ^ ((16 / 135 : ℝ)
              + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)) then 3 * e ^ 2 else 0) := by
    intro p hp
    obtain ⟨hpr, hpa, hpb⟩ := hwin p hp
    by_cases hsmall : (p : ℝ) ≤ Y ^ ((16 / 135 : ℝ)
        + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ))
    · rw [if_pos hsmall]
      have h1 := inner_le_psi_small (Y := Y) (n := n) (p := p) (K := K) (e := e) hY hK2 hbig
        he hstep hpr hpa hpb hsmall
      have hL : 0 ≤ Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ ha, le_div_iff₀ hlogY]
        have h2 : Real.log (Y ^ (16 / 135 : ℝ)) < Real.log (p : ℝ) :=
          Real.log_lt_log (Real.rpow_pos_of_pos hY0 _) hpa
        rw [Real.log_rpow hY0] at h2
        linarith
      have h3 : 0 ≤ (1 / 2) * Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) ^ 2
          + Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) * e := by
        have h4 : 0 ≤ Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) * e :=
          mul_nonneg hL he0
        nlinarith [sq_nonneg (Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)))]
      linarith
    · rw [if_neg hsmall]
      have hlarge : Y ^ ((16 / 135 : ℝ) + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ))
          < (p : ℝ) := not_le.mp hsmall
      have h1 := inner_le_psi_big (Y := Y) (n := n) (p := p) (K := K) (e := e) hY hK2 hbig
        he hstep hpr hpa hpb hlarge
      linarith
  -- split the weight into the outer staircase plus the first block
  have hstepA : (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
        Nat.Prime,
        (1 : ℝ) / (p : ℝ) * (∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
            Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)),
            (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y))))
      ≤ ∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
          Nat.Prime,
          (1 : ℝ) / (p : ℝ) * (((1 / 2) * Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) ^ 2
              + Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) * e)
            + (if (p : ℝ) ≤ Y ^ ((16 / 135 : ℝ)
                + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)) then 3 * e ^ 2 else 0)) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hp0 : (0 : ℝ) ≤ (1 : ℝ) / (p : ℝ) := by
      have hpp : p.Prime := (hwin p hp).1
      have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
      positivity
    exact mul_le_mul_of_nonneg_left (hpoint p hp) hp0
  have hstepB : (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
        Nat.Prime,
        (1 : ℝ) / (p : ℝ) * (((1 / 2) * Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) ^ 2
            + Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) * e)
          + (if (p : ℝ) ≤ Y ^ ((16 / 135 : ℝ)
              + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)) then 3 * e ^ 2 else 0)))
      = (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
          Nat.Prime,
          (1 : ℝ) / (p : ℝ) * ((1 / 2) * Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) ^ 2
            + Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) * e))
        + (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
            Nat.Prime,
            (1 : ℝ) / (p : ℝ) * (if (p : ℝ) ≤ Y ^ ((16 / 135 : ℝ)
                + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)) then 3 * e ^ 2 else 0)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    ring
  have hite : (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
        Nat.Prime,
        (1 : ℝ) / (p : ℝ) * (if (p : ℝ) ≤ Y ^ ((16 / 135 : ℝ)
            + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)) then 3 * e ^ 2 else 0))
      ≤ 3 * e ^ 2 * S := by
    have h1 : (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
        Nat.Prime,
        (1 : ℝ) / (p : ℝ) * (if (p : ℝ) ≤ Y ^ ((16 / 135 : ℝ)
            + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)) then 3 * e ^ 2 else 0))
        ≤ ∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
            Nat.Prime, (1 : ℝ) / (p : ℝ) * (3 * e ^ 2) := by
      refine Finset.sum_le_sum (fun p hp => ?_)
      have hp0 : (0 : ℝ) ≤ (1 : ℝ) / (p : ℝ) := by positivity
      by_cases h : (p : ℝ) ≤ Y ^ ((16 / 135 : ℝ)
          + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ))
      · rw [if_pos h]
      · rw [if_neg h]
        have h3 : (0 : ℝ) ≤ 3 * e ^ 2 := by positivity
        calc (1 : ℝ) / (p : ℝ) * 0 = 0 := by ring
          _ ≤ (1 : ℝ) / (p : ℝ) * (3 * e ^ 2) := by positivity
    have h2 : (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
        Nat.Prime, (1 : ℝ) / (p : ℝ) * (3 * e ^ 2)) ≤ 3 * e ^ 2 * S := by
      rw [← Finset.sum_mul]
      have h3 := mul_le_mul_of_nonneg_right hS (by positivity : (0 : ℝ) ≤ 3 * e ^ 2)
      nlinarith [h3]
    linarith [h1, h2]
  -- assemble: split, per-prime bound, outer staircase, first block
  have houter := outer_full_le (Y := Y) (K := K) (e := e) hY hK2 hbig he hstep
  have hfin : (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
        Nat.Prime,
        (1 : ℝ) / (p : ℝ) * (((1 / 2) * Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) ^ 2
            + Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) * e)
          + (if (p : ℝ) ≤ Y ^ ((16 / 135 : ℝ)
              + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)) then 3 * e ^ 2 else 0)))
      ≤ (Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 3 / 6
          + e * (Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 2
              + Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) * e)) + 3 * e ^ 2 * S := by
    calc (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
          Nat.Prime,
          (1 : ℝ) / (p : ℝ) * (((1 / 2) * Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) ^ 2
              + Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) * e)
            + (if (p : ℝ) ≤ Y ^ ((16 / 135 : ℝ)
                + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)) then 3 * e ^ 2 else 0)))
        = (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
            Nat.Prime,
            (1 : ℝ) / (p : ℝ) * ((1 / 2) * Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) ^ 2
              + Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) * e))
          + (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
              Nat.Prime,
              (1 : ℝ) / (p : ℝ) * (if (p : ℝ) ≤ Y ^ ((16 / 135 : ℝ)
                  + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)) then 3 * e ^ 2 else 0)) := hstepB
      _ ≤ (Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 3 / 6
            + e * (Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 2
                + Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) * e)) + 3 * e ^ 2 * S := by
          linarith [houter, hite]
  have h1 := pair_sum_split_le (Y := Y) hY n
  linarith [h1, hstepA, hfin]

/-- Below `71/405` the upper branch is **empty**: every `q < p` still has `p q² < Y^(71/135)`,
because `3·(71/405) = 71/135`. -/
private theorem upper_low_empty {Y : ℝ} {n p : ℕ} (hY : 1 < Y)
    (hlow : (p : ℝ) ≤ Y ^ (71 / 405 : ℝ)) :
    (∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
        Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)),
        (if (p : ℝ) * (q : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0
          else (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y))))
      = 0 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  refine Finset.sum_eq_zero (fun q hq => ?_)
  obtain ⟨-, hpr, hqa, hqp⟩ := Finset.mem_filter.mp hq
  have hp0' : (0 : ℝ) < (p : ℝ) := by
    have h1 : (0 : ℝ) < Y ^ (16 / 135 : ℝ) := Real.rpow_pos_of_pos hY0 _
    have h2 : Y ^ (16 / 135 : ℝ) < (p : ℝ) :=
      lt_of_le_of_lt hqa hqp
    linarith
  have hqlt : (q : ℝ) < (p : ℝ) := hqp
  rw [if_pos]
  -- `p q² < p³ ≤ (Y^(71/405))³ = Y^(71/135)`
  have hq2 : (q : ℝ) ^ 2 < (p : ℝ) ^ 2 := by
    have hq0 : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hY0 _) hqa
    nlinarith [hqlt, hq0, hp0']
  have h1 : (p : ℝ) * (q : ℝ) ^ 2 < (p : ℝ) * (p : ℝ) ^ 2 :=
    mul_lt_mul_of_pos_left hq2 hp0'
  have h2 : (p : ℝ) * (p : ℝ) ^ 2 = (p : ℝ) ^ 3 := by ring
  have h3 : (p : ℝ) ^ 3 ≤ (Y ^ (71 / 405 : ℝ)) ^ 3 := by
    apply pow_le_pow_left₀ (le_of_lt hp0') hlow
  have h4 : (Y ^ (71 / 405 : ℝ)) ^ 3 = Y ^ (71 / 135 : ℝ) := by
    rw [← Real.rpow_natCast (Y ^ (71 / 405 : ℝ)) 3, ← Real.rpow_mul (le_of_lt hY0)]
    norm_num
  linarith [h1, h2, h3, h4]

/-- `Y ^ (log p / log Y) = p`. -/
private theorem rpow_log_div {Y : ℝ} {p : ℕ} (hY : 1 < Y) (hp : p.Prime) :
    Y ^ (Real.log (p : ℝ) / Real.log Y) = (p : ℝ) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  rw [Real.rpow_def_of_pos hY0]
  rw [mul_div_cancel₀ _ hlogY.ne']
  exact Real.exp_log hp0

/-- The sharp branch dominates the `Ioc` window: every prime up to `Y^cap` still satisfies
`p q² ≤ Y^(71/135)`, because `x + 2·cap = 71/135`. -/
private theorem upper_sharp_ge {Y : ℝ} {n p : ℕ} {x cap : ℝ} (hY : 1 < Y) (hp : p.Prime)
    (hn : 2 * Y ≤ (n : ℝ))
    (hx : x = Real.log (p : ℝ) / Real.log Y)
    (hcap : cap = (71 / 135 - x) / 2) (hcapx : cap < x) :
    (∑ q ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ cap⌋₊).filter Nat.Prime,
        (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y)))
      ≤ (∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
          Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)),
          (if (p : ℝ) * (q : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then
            (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y))
            else 0)) := by
  classical
  have hY0 : (0 : ℝ) < Y := by linarith
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpx : Y ^ x = (p : ℝ) := by rw [hx]; exact rpow_log_div hY hp
  refine le_trans (Finset.sum_le_sum (fun q hq => ?_))
    (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
  · -- the window satisfies the branch condition
    rw [if_pos]
    obtain ⟨hmem, hqr⟩ := Finset.mem_filter.mp hq
    have hqle : (q : ℝ) ≤ Y ^ cap := by
      have h1 : ((q : ℕ) : ℝ) ≤ ((⌊Y ^ cap⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast (Finset.mem_Ioc.mp hmem).2
      have h2 : ((⌊Y ^ cap⌋₊ : ℕ) : ℝ) ≤ Y ^ cap :=
        Nat.floor_le (le_of_lt (Real.rpow_pos_of_pos hY0 _))
      linarith
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
    have hYcap0 : (0 : ℝ) < Y ^ cap := Real.rpow_pos_of_pos hY0 _
    have hq2 : (q : ℝ) ^ 2 ≤ (Y ^ cap) ^ 2 := by nlinarith [hqle, hq0, hYcap0]
    have h1 : (p : ℝ) * (q : ℝ) ^ 2 ≤ (p : ℝ) * (Y ^ cap) ^ 2 :=
      mul_le_mul_of_nonneg_left hq2 (le_of_lt hp0)
    have h2 : (p : ℝ) * (Y ^ cap) ^ 2 = Y ^ (71 / 135 : ℝ) := by
      have h3 : (Y ^ cap) ^ 2 = Y ^ (cap + cap) := by rw [Real.rpow_add hY0, sq]
      rw [h3, ← hpx, ← Real.rpow_add hY0]
      congr 1
      rw [hcap]; ring
    linarith [h1, h2]
  · -- and sits inside the model filter
    intro q hq
    obtain ⟨hmem, hqr⟩ := Finset.mem_filter.mp hq
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hmem
    have hqa : Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) := by
      have h1 : ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) < (q : ℝ) := by exact_mod_cast hlo
      have h2 : Y ^ (16 / 135 : ℝ) < ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      have h3 : ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) + 1 ≤ (q : ℝ) := by
        have h4 : ⌊Y ^ (16 / 135 : ℝ)⌋₊ + 1 ≤ q := hlo
        exact_mod_cast h4
      linarith
    have hqle : (q : ℝ) ≤ Y ^ cap := by
      have h1 : ((q : ℕ) : ℝ) ≤ ((⌊Y ^ cap⌋₊ : ℕ) : ℝ) := by exact_mod_cast hhi
      have h2 : ((⌊Y ^ cap⌋₊ : ℕ) : ℝ) ≤ Y ^ cap :=
        Nat.floor_le (le_of_lt (Real.rpow_pos_of_pos hY0 _))
      linarith
    have hqp : (q : ℝ) < (p : ℝ) := by
      have h3 : Y ^ cap < Y ^ x := Real.rpow_lt_rpow_of_exponent_lt hY hcapx
      linarith [hpx]
    have hqn : q ∈ Finset.range (n + 1) := by
      rw [Finset.mem_range]
      have h4 : Y ^ cap ≤ Y ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hY.le (by rw [hcap]; nlinarith)
      rw [Real.rpow_one] at h4
      have h6 : (q : ℝ) ≤ (n : ℝ) := by linarith
      have h7 : q ≤ n := by exact_mod_cast h6
      omega
    exact Finset.mem_filter.mpr ⟨hqn, hqr, hqa, hqp⟩
  · intro q hq _
    have hqa : Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) := (Finset.mem_filter.mp hq).2.2.1
    have hq0 : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hY0 _) hqa
    have hlogY : 0 < Real.log Y := Real.log_pos hY
    have hden : (0 : ℝ) < (16 / 135) * Real.log Y := by
      have h2 : (0 : ℝ) < 16 / 135 := by norm_num
      positivity
    have hratio : (1 : ℝ) ≤ Real.log (q : ℝ) / ((16 / 135) * Real.log Y) := by
      rw [le_div_iff₀ hden]
      have hl : Real.log (Y ^ (16 / 135 : ℝ)) ≤ Real.log (q : ℝ) :=
        Real.log_le_log (Real.rpow_pos_of_pos hY0 _) hqa
      rw [Real.log_rpow hY0] at hl
      linarith
    have hlog0 : 0 ≤ Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y)) :=
      Real.log_nonneg hratio
    by_cases hc : (p : ℝ) * (q : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ)
    · rw [if_pos hc]
      exact mul_nonneg (by positivity) hlog0
    · rw [if_neg hc]

/-- The upper branch at one outer prime: `U_p ≤ φ₃(x_p) + 10e`.  Above `71/405` the full inner
sum is `inner_le_psi_big`, the sharp part is at least `inner_q_sum_ge` on the `Ioc` window
(contained in the sharp filter by `upper_sharp_ge`), and the two `ψ`s differ by `φ₃` plus an
`O(e)` correction. -/
private theorem upper_point_le {Y : ℝ} {n p K : ℕ} {e : ℝ} (hY : 1 < Y) (hK2 : 2 ≤ K)
    (hbig : 2 * Real.log 2 ≤ (16 / 135) * Real.log Y)
    (he : e = (89 / 462 - 0.00000001 - 16 / 135) / ((16 / 135) * (K : ℝ))
            + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)))
    (he1 : e ≤ 1)
    (hstep : 2 ≤ Y ^ (16 / 135 : ℝ) *
      (Y ^ ((89 / 462 - 0.00000001 - 16 / 135) / ((K : ℝ) ^ 2)) - 1))
    (hn : 2 * Y ≤ (n : ℝ))
    (hp : p.Prime) (hpa : Y ^ (16 / 135 : ℝ) < (p : ℝ))
    (hpb : (p : ℝ) ≤ Y ^ (89 / 462 - 0.00000001 : ℝ)) :
    (∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
        Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)),
        (if (p : ℝ) * (q : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0
          else (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y))))
      ≤ (if (p : ℝ) ≤ Y ^ (71 / 405 : ℝ) then 0
          else (1 / 2) * (Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) ^ 2
            - Real.log (((71 / 135 - Real.log (p : ℝ) / Real.log Y) / 2) / (16 / 135)) ^ 2))
        + 10 * e := by
  classical
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have ha : (0 : ℝ) < 16 / 135 := by norm_num
  have hd : (0 : ℝ) < 89 / 462 - 0.00000001 - 16 / 135 := by norm_num
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hK2' : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK2
  have he0 : 0 ≤ e := by rw [he]; positivity
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  set x : ℝ := Real.log (p : ℝ) / Real.log Y with hx
  have hxle : x ≤ 89 / 462 - 0.00000001 := by
    have h1 : Real.log (p : ℝ) ≤ Real.log (Y ^ (89 / 462 - 0.00000001 : ℝ)) :=
      Real.log_le_log hp0 hpb
    rw [Real.log_rpow hY0] at h1
    rw [hx, div_le_iff₀ hlogY]
    linarith
  by_cases hlow : (p : ℝ) ≤ Y ^ (71 / 405 : ℝ)
  · rw [if_pos hlow, upper_low_empty hY hlow]
    linarith
  · rw [if_neg hlow]
    have hpgt : Y ^ (71 / 405 : ℝ) < (p : ℝ) := not_le.mp hlow
    have hxgt2 : (71 / 405 : ℝ) < x := by
      have h1 : Real.log (Y ^ (71 / 405 : ℝ)) < Real.log (p : ℝ) :=
        Real.log_lt_log (Real.rpow_pos_of_pos hY0 _) hpgt
      rw [Real.log_rpow hY0] at h1
      rw [hx, lt_div_iff₀ hlogY]
      linarith
    have hlarge : Y ^ ((16 / 135 : ℝ) + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ))
        < (p : ℝ) := by
      have hdiv : (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)
          ≤ (89 / 462 - 0.00000001 - 16 / 135) / 2 := by
        rw [div_le_div_iff₀ hKpos (by norm_num : (0 : ℝ) < 2)]
        nlinarith [hd, hKpos, hK2']
      have h2 : (16 / 135 : ℝ) + (89 / 462 - 0.00000001 - 16 / 135) / 2 ≤ 71 / 405 := by
        norm_num
      have hexp : (16 / 135 : ℝ) + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ) ≤ 71 / 405 := by
        linarith [hdiv, h2]
      calc Y ^ ((16 / 135 : ℝ) + (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ))
          ≤ Y ^ (71 / 405 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY.le hexp
        _ < (p : ℝ) := hpgt
    set cap : ℝ := (71 / 135 - x) / 2 with hcap
    have hcap1 : 16 / 135 ≤ cap := by rw [hcap]; linarith
    have hcap2 : cap ≤ 89 / 462 - 0.00000001 := by rw [hcap]; linarith
    have hcapx : cap < x := by rw [hcap]; linarith
    have hcap0 : (0 : ℝ) < cap := lt_of_lt_of_le ha hcap1
    -- the inner facts
    have hF := inner_le_psi_big (Y := Y) (n := n) (p := p) (K := K) (e := e) hY hK2 hbig he
      hstep hp hpa hpb hlarge
    have hmesh : ∀ i : ℕ, i < K →
        ⌈Y ^ (16 / 135 + (i : ℝ) * ((cap - 16 / 135) / (K : ℝ)))⌉₊
          ≤ ⌊Y ^ (16 / 135 + ((i : ℝ) + 1) * ((cap - 16 / 135) / (K : ℝ)))⌋₊ := by
      intro i _
      have hW : (0 : ℝ) ≤ (cap - 16 / 135) / (K : ℝ) :=
        div_nonneg (by linarith) (le_of_lt hKpos)
      have hw0 : (89 / 462 - 0.00000001 - 16 / 135) / ((K : ℝ) ^ 2)
          ≤ (cap - 16 / 135) / (K : ℝ) := by
        rw [div_le_div_iff₀ (by positivity) hKpos]
        nlinarith [hd, hKpos, hK2', hcap2]
      exact mesh_cond (a := 16 / 135) (W := (cap - 16 / 135) / (K : ℝ))
        (w0 := (89 / 462 - 0.00000001 - 16 / 135) / ((K : ℝ) ^ 2)) hY hW
        (by positivity) hw0 hstep i
    have hS0 := inner_q_sum_ge (Y := Y) (K := K) (μ := cap) hY (by omega) hcap1 hcap2 hbig hmesh
    -- convert the `Ioc` window's weight to the model's spelling
    have hcvIoc : (∑ q ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ cap⌋₊).filter Nat.Prime,
          (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y)))
        = (∑ q ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ cap⌋₊).filter Nat.Prime,
          (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / Real.log Y / (16 / 135))) := by
      refine Finset.sum_congr rfl (fun q hq => ?_)
      have hq0 : (0 : ℝ) < (q : ℝ) := by
        have h1 : ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) < (q : ℝ) := by
          exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).1
        have h2 : (0 : ℝ) ≤ ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) := by positivity
        linarith
      rw [log_arg_div hq0 hlogY]
    have hS1 : (1 / 2) * Real.log (cap / (16 / 135)) ^ 2
        - Real.log (cap / (16 / 135))
          * ((cap - 16 / 135) / ((16 / 135) * (K : ℝ))
            + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)))
        ≤ (∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
            Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)),
            (if (p : ℝ) * (q : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then
              (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y))
              else 0)) := by
      refine le_trans ?_ (upper_sharp_ge (Y := Y) (n := n) (p := p) (x := x) (cap := cap)
        hY hp hn hx hcap hcapx)
      rw [hcvIoc]
      exact hS0
    -- `F_p = S_p + U_p`
    have hFU : (∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
          Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)),
          (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y)))
        = (∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
            Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)),
            (if (p : ℝ) * (q : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then
              (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y))
              else 0))
          + (∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
              Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)),
              (if (p : ℝ) * (q : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0
                else (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y)))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      split_ifs <;> ring
    -- `Lx, Lc ≤ 1` and `e_cap ≤ e`
    have hLx1 : Real.log (x / (16 / 135)) ≤ 1 := by
      have h1 : Real.log (x / (16 / 135)) ≤ Real.log ((89 / 462 : ℝ) / (16 / 135)) := by
        apply Real.log_le_log (by positivity)
        apply div_le_div_of_nonneg_right _ (le_of_lt ha)
        linarith
      have h2 : Real.log ((89 / 462 : ℝ) / (16 / 135)) ≤ Real.log 2 :=
        Real.log_le_log (by norm_num) (by norm_num)
      have h4 : Real.log (2 : ℝ) ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      linarith
    have hLc1 : Real.log (cap / (16 / 135)) ≤ 1 := by
      have h1 : Real.log (cap / (16 / 135)) ≤ Real.log ((89 / 462 : ℝ) / (16 / 135)) := by
        apply Real.log_le_log (by positivity)
        apply div_le_div_of_nonneg_right _ (le_of_lt ha)
        linarith
      have h2 : Real.log ((89 / 462 : ℝ) / (16 / 135)) ≤ Real.log 2 :=
        Real.log_le_log (by norm_num) (by norm_num)
      have h4 : Real.log (2 : ℝ) ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      linarith
    have hLc0 : 0 ≤ Real.log (cap / (16 / 135)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ ha]
      linarith
    have hecap : (cap - 16 / 135) / ((16 / 135) * (K : ℝ))
        + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)) ≤ e := by
      rw [he]
      have h1 : (cap - 16 / 135) / ((16 / 135) * (K : ℝ))
          ≤ (89 / 462 - 0.00000001 - 16 / 135) / ((16 / 135) * (K : ℝ)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      linarith
    have hx' : Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135))
        = Real.log (x / (16 / 135)) := by rw [← hx]
    have hcap' : Real.log (((71 / 135 - Real.log (p : ℝ) / Real.log Y) / 2) / (16 / 135))
        = Real.log (cap / (16 / 135)) := by rw [← hx, ← hcap]
    rw [hx', hcap']
    have hU : (∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
          Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)),
          (if (p : ℝ) * (q : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0
            else (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y))))
        ≤ ((1 / 2) * Real.log (x / (16 / 135)) ^ 2 + Real.log (x / (16 / 135)) * e)
          - ((1 / 2) * Real.log (cap / (16 / 135)) ^ 2
            - Real.log (cap / (16 / 135))
              * ((cap - 16 / 135) / ((16 / 135) * (K : ℝ))
                + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)))) := by
      linarith [hFU, hF, hS1]
    have h2 : Real.log (x / (16 / 135)) * e ≤ 1 * e :=
      mul_le_mul_of_nonneg_right hLx1 he0
    have h3 : Real.log (cap / (16 / 135))
        * ((cap - 16 / 135) / ((16 / 135) * (K : ℝ))
          + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y))) ≤ 1 * e := by
      have h1 : Real.log (cap / (16 / 135))
          * ((cap - 16 / 135) / ((16 / 135) * (K : ℝ))
            + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)))
          ≤ Real.log (cap / (16 / 135)) * e := mul_le_mul_of_nonneg_left hecap hLc0
      have h4 : Real.log (cap / (16 / 135)) * e ≤ 1 * e :=
        mul_le_mul_of_nonneg_right hLc1 he0
      linarith
    linarith [hU, h2, h3, he0]
/-- The upper-branch pair sum splits over the outer prime. -/
private theorem upper_pair_split_le {Y : ℝ} {n : ℕ} (hY : 1 < Y) :
    (∑ pq ∈ (Source565.pairDomain true Y n).filter
        (fun pq => ¬ ((pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ))),
        (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
          * Real.log (Real.log (pq.2 : ℝ) / ((16 / 135) * Real.log Y)))
      ≤ ∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ) *
            (∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
                Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)),
              (if (p : ℝ) * (q : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0
                else (1 : ℝ) / (q : ℝ)
                  * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y)))) := by
  classical
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  -- the fibre split of the upper-branch sum
  set W : Finset ℕ :=
    (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter Nat.Prime with hW
  set T : ℕ → Finset ℕ := fun p => (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
    Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)) with hT
  have hcond : ∀ pq ∈ Source565.pairDomain true Y n,
      ((pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ)) ↔
      ((pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ)) := fun _ _ => Iff.rfl
  have hmaps : ∀ x ∈ Source565.pairDomain true Y n, x.1 ∈ W := by
    intro x hx
    obtain ⟨p, q⟩ := x
    obtain ⟨hmem, hconds⟩ := Finset.mem_filter.mp hx
    obtain ⟨hpr, hαp, hsp, hqr, hαq, hqmin, hgrp, hdec, hβp⟩ := hconds
    rw [hW, Finset.mem_filter]
    refine ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hpr⟩
    · have h1 : ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) ≤ Y ^ (16 / 135 : ℝ) :=
        Nat.floor_le (le_of_lt (Real.rpow_pos_of_pos hY0 _))
      have h2 : ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) < (p : ℝ) := lt_of_le_of_lt h1 hαp
      exact Nat.cast_lt.mp h2
    · exact Nat.le_floor (hβp rfl)
  have hfib : ∀ p : ℕ, (Source565.pairDomain true Y n).filter (fun x => x.1 = p)
      = ((T p).filter (fun q => (p, q) ∈ Source565.pairDomain true Y n)).image (fun q => (p, q)) := by
    intro p
    ext x
    obtain ⟨p', q'⟩ := x
    constructor
    · intro hx
      obtain ⟨hxmem, hx1⟩ := Finset.mem_filter.mp hx
      have hx1' : p' = p := hx1
      subst hx1'
      refine Finset.mem_image.mpr ⟨q', ?_, rfl⟩
      obtain ⟨hmem, hconds⟩ := Finset.mem_filter.mp hxmem
      obtain ⟨hpr, hαp, hsp, hqr, hαq, hqmin, hgrp, hdec, hβp⟩ := hconds
      refine Finset.mem_filter.mpr ⟨?_, hxmem⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by
          have := (Finset.mem_product.mp hmem).2
          simpa using this), hqr, le_of_lt hαq, lt_of_lt_of_le hqmin (min_le_left _ _)⟩
    · intro hx
      obtain ⟨q, hq, hqx⟩ := Finset.mem_image.mp hx
      obtain ⟨hqp, hqq⟩ : p = p' ∧ q = q' := Prod.mk.inj hqx
      subst hqp
      subst hqq
      obtain ⟨-, hqpD⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hqpD, rfl⟩
  have hstepA : (∑ pq ∈ (Source565.pairDomain true Y n).filter
        (fun pq => ¬ ((pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ))),
        (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
          * Real.log (Real.log (pq.2 : ℝ) / ((16 / 135) * Real.log Y)))
      ≤ ∑ pq ∈ Source565.pairDomain true Y n,
          (if (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0
            else (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
              * Real.log (Real.log (pq.2 : ℝ) / ((16 / 135) * Real.log Y))) := by
    have hconv : (∑ x ∈ (Source565.pairDomain true Y n).filter
          (fun pq => ¬ ((pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ))),
          (if (x.1 : ℝ) * (x.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0
            else (1 : ℝ) / ((x.1 : ℝ) * (x.2 : ℝ))
              * Real.log (Real.log (x.2 : ℝ) / ((16 / 135) * Real.log Y))))
        = (∑ x ∈ (Source565.pairDomain true Y n).filter
            (fun pq => ¬ ((pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ))),
            (1 : ℝ) / ((x.1 : ℝ) * (x.2 : ℝ))
              * Real.log (Real.log (x.2 : ℝ) / ((16 / 135) * Real.log Y))) := by
      refine Finset.sum_congr rfl (fun x hx => ?_)
      rw [if_neg (Finset.mem_filter.mp hx).2]
    rw [← hconv]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro x hx _
    by_cases hc : (x.1 : ℝ) * (x.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ)
    · rw [if_pos hc]
    · rw [if_neg hc]
      have hqa : Y ^ (16 / 135 : ℝ) ≤ (x.2 : ℝ) := by
        have h1 := (Finset.mem_filter.mp hx).2.2.2.2.2.1
        exact le_of_lt h1
      have hx2 : (0 : ℝ) < (x.2 : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hY0 _) hqa
      have hden : (0 : ℝ) < (16 / 135) * Real.log Y := by
        have h2 : (0 : ℝ) < 16 / 135 := by norm_num
        have h3 : (0 : ℝ) < Real.log Y := Real.log_pos hY
        positivity
      have hratio : (1 : ℝ) ≤ Real.log (x.2 : ℝ) / ((16 / 135) * Real.log Y) := by
        rw [le_div_iff₀ hden]
        have hl : Real.log (Y ^ (16 / 135 : ℝ)) ≤ Real.log (x.2 : ℝ) :=
          Real.log_le_log (Real.rpow_pos_of_pos hY0 _) hqa
        rw [Real.log_rpow hY0] at hl
        linarith
      have hlog0 : 0 ≤ Real.log (Real.log (x.2 : ℝ) / ((16 / 135) * Real.log Y)) :=
        Real.log_nonneg hratio
      exact mul_nonneg (by positivity) hlog0
  have hfib_le : ∀ p ∈ W,
      (∑ x ∈ (Source565.pairDomain true Y n).filter (fun x => x.1 = p),
          (if (x.1 : ℝ) * (x.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0
            else (1 : ℝ) / ((x.1 : ℝ) * (x.2 : ℝ))
              * Real.log (Real.log (x.2 : ℝ) / ((16 / 135) * Real.log Y))))
        ≤ (1 : ℝ) / (p : ℝ) *
          (∑ q ∈ T p, (if (p : ℝ) * (q : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0
            else (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y)))) := by
    intro p hp
    rw [hfib p]
    rw [Finset.sum_image (g := fun q => (p, q))
      (f := fun x : ℕ × ℕ => (if (x.1 : ℝ) * (x.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0
        else (1 : ℝ) / ((x.1 : ℝ) * (x.2 : ℝ))
          * Real.log (Real.log (x.2 : ℝ) / ((16 / 135) * Real.log Y))))
      (by intro x _ y _ h; exact (Prod.mk.inj h).2)]
    dsimp only
    rw [Finset.mul_sum]
    have hsummand : ∀ q : ℕ,
        (if (p : ℝ) * (q : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0
          else (1 : ℝ) / ((p : ℝ) * (q : ℝ))
            * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y)))
        = (1 : ℝ) / (p : ℝ) * (if (p : ℝ) * (q : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0
          else (1 : ℝ) / (q : ℝ)
            * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y))) := by
      intro q
      by_cases hc : (p : ℝ) * (q : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ)
      · rw [if_pos hc, if_pos hc, mul_zero]
      · rw [if_neg hc, if_neg hc]
        field_simp
    simp only [hsummand]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro q hq
      exact (Finset.mem_filter.mp hq).1
    · intro q hq _
      by_cases hc : (p : ℝ) * (q : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ)
      · rw [if_pos hc]
        simp
      · rw [if_neg hc]
        have hqa : Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) := (Finset.mem_filter.mp hq).2.2.1
        have hq0 : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hY0 _) hqa
        have hden : (0 : ℝ) < (16 / 135) * Real.log Y := by
          have h2 : (0 : ℝ) < 16 / 135 := by norm_num
          positivity
        have hratio : (1 : ℝ) ≤ Real.log (q : ℝ) / ((16 / 135) * Real.log Y) := by
          rw [le_div_iff₀ hden]
          have hl : Real.log (Y ^ (16 / 135 : ℝ)) ≤ Real.log (q : ℝ) :=
            Real.log_le_log (Real.rpow_pos_of_pos hY0 _) hqa
          rw [Real.log_rpow hY0] at hl
          linarith
        have hlog0 : 0 ≤ Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y)) :=
          Real.log_nonneg hratio
        exact mul_nonneg (by positivity) (mul_nonneg (by positivity) hlog0)
  have hstepB : (∑ pq ∈ Source565.pairDomain true Y n,
          (if (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0
            else (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
              * Real.log (Real.log (pq.2 : ℝ) / ((16 / 135) * Real.log Y))))
      ≤ ∑ p ∈ W, (1 : ℝ) / (p : ℝ) *
          (∑ q ∈ T p, (if (p : ℝ) * (q : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0
            else (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y)))) := by
    rw [← Finset.sum_fiberwise_of_maps_to (t := W) hmaps
      (fun x : ℕ × ℕ => (if (x.1 : ℝ) * (x.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0
        else (1 : ℝ) / ((x.1 : ℝ) * (x.2 : ℝ))
          * Real.log (Real.log (x.2 : ℝ) / ((16 / 135) * Real.log Y))))]
    exact Finset.sum_le_sum hfib_le
  -- assemble through the per-prime bound and the staircase
  linarith [hstepA, hstepB]
/-- The `φ₃` staircase: `φ₃` is `max 0 g` with `g x = ½[log(x/a)² − log(cap(x)/a)²]`, its
integral over `[a,b]` is `∫_{71/405}^b g/x`, and `prime_sum_block_le` applies to it. -/
private theorem upper_stair_le {Y : ℝ} {K : ℕ} {e : ℝ} (hY : 1 < Y) (hK2 : 2 ≤ K)
    (hbig : 2 * Real.log 2 ≤ (16 / 135) * Real.log Y)
    (he : e = (89 / 462 - 0.00000001 - 16 / 135) / ((16 / 135) * (K : ℝ))
            + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)))
    (hstep : 2 ≤ Y ^ (16 / 135 : ℝ) *
      (Y ^ ((89 / 462 - 0.00000001 - 16 / 135) / ((K : ℝ) ^ 2)) - 1)) :
    (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ) * max 0 ((1 / 2) * (Real.log ((Real.log (p : ℝ) / Real.log Y)
            / (16 / 135)) ^ 2
          - Real.log (((71 / 135 - Real.log (p : ℝ) / Real.log Y) / 2) / (16 / 135)) ^ 2)))
      ≤ (1 / 2) * ((∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001 : ℝ),
            Real.log (u / (16 / 135)) ^ 2 / u)
          - (∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001 : ℝ),
            Real.log (((71 / 135 - u) / 2) / (16 / 135)) ^ 2 / u))
        + (max 0 ((1 / 2) * (Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 2
              - Real.log (((71 / 135 - (89 / 462 - 0.00000001 : ℝ)) / 2) / (16 / 135)) ^ 2)))
          * e := by
  classical
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have ha : (0 : ℝ) < 16 / 135 := by norm_num
  have hab : (16 / 135 : ℝ) ≤ 89 / 462 - 0.00000001 := by norm_num
  have he0 : 0 ≤ e := by rw [he]; positivity
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hK2' : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK2
  have hd : (0 : ℝ) < 89 / 462 - 0.00000001 - 16 / 135 := by norm_num
  -- `φ₃` and its elementary `g`
  set g : ℝ → ℝ := fun x => (1 / 2) * (Real.log (x / (16 / 135)) ^ 2
    - Real.log (((71 / 135 - x) / 2) / (16 / 135)) ^ 2) with hg
  set Phi : ℝ → ℝ := fun x => max 0 (g x) with hPhi
  have hgmono : ∀ x y : ℝ, 16 / 135 ≤ x → x ≤ y → y ≤ 89 / 462 - 0.00000001 → g x ≤ g y := by
    intro x y hx hxy hy
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha hx
    have hL : Real.log (x / (16 / 135)) ≤ Real.log (y / (16 / 135)) :=
      Real.log_le_log (div_pos hx0 (by norm_num)) (by gcongr)
    have hL0 : 0 ≤ Real.log (x / (16 / 135)) := Real.log_nonneg (by
      rw [le_div_iff₀ ha]; linarith)
    have hLc : Real.log (((71 / 135 - y) / 2) / (16 / 135))
        ≤ Real.log (((71 / 135 - x) / 2) / (16 / 135)) := by
      have hy0 : (0 : ℝ) < (71 / 135 - y) / 2 := by linarith
      apply Real.log_le_log (div_pos hy0 (by norm_num))
      apply div_le_div_of_nonneg_right _ (le_of_lt ha)
      linarith
    have hLc0 : 0 ≤ Real.log (((71 / 135 - y) / 2) / (16 / 135)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ ha]
      linarith
    have h1 : Real.log (x / (16 / 135)) ^ 2 ≤ Real.log (y / (16 / 135)) ^ 2 :=
      pow_le_pow_left₀ hL0 hL 2
    have h2 : Real.log (((71 / 135 - y) / 2) / (16 / 135)) ^ 2
        ≤ Real.log (((71 / 135 - x) / 2) / (16 / 135)) ^ 2 :=
      pow_le_pow_left₀ hLc0 hLc 2
    simp only [hg]
    linarith
  have hmono : ∀ x y : ℝ, 16 / 135 ≤ x → x ≤ y → y ≤ 89 / 462 - 0.00000001 → Phi x ≤ Phi y := by
    intro x y hx hxy hy
    have h := hgmono x y hx hxy hy
    simp only [hPhi]
    exact max_le_max le_rfl h
  have hnn : ∀ x : ℝ, 16 / 135 ≤ x → x ≤ 89 / 462 - 0.00000001 → 0 ≤ Phi x := by
    intro x _ _
    simp only [hPhi]
    exact le_max_left 0 (g x)
  have hlog1 : ContinuousOn (fun x : ℝ => Real.log (x / (16 / 135)))
      (Set.Icc (16 / 135) (89 / 462 - 0.00000001)) := by
    apply ContinuousOn.log (by fun_prop)
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha hx.1
    exact div_ne_zero hx0.ne' (by norm_num)
  have hlog2 : ContinuousOn (fun x : ℝ => Real.log (((71 / 135 - x) / 2) / (16 / 135)))
      (Set.Icc (16 / 135) (89 / 462 - 0.00000001)) := by
    apply ContinuousOn.log (by fun_prop)
    intro x hx
    exact (div_pos (by linarith [hx.2]) (by norm_num)).ne'
  have hcont : ContinuousOn (fun x : ℝ => g x) (Set.Icc (16 / 135) (89 / 462 - 0.00000001)) := by
    simp only [hg]
    exact continuousOn_const.mul ((hlog1.pow 2).sub (hlog2.pow 2))
  have hint : ∀ u v : ℝ, 16 / 135 ≤ u → u ≤ v → v ≤ 89 / 462 - 0.00000001 →
      IntervalIntegrable (fun x : ℝ => Phi x / x) MeasureTheory.volume u v := by
    intro u v hu huv hv
    apply ContinuousOn.intervalIntegrable_of_Icc huv
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le ha hu
    have hsub : Set.Icc u v ⊆ Set.Icc (16 / 135) (89 / 462 - 0.00000001) :=
      Set.Icc_subset_Icc hu hv
    have hcontmax : ContinuousOn (fun x : ℝ => Phi x) (Set.Icc u v) := by
      simp only [hPhi]
      have hmax : (fun x : ℝ => max 0 (g x)) = fun x => (g x + |g x|) / 2 := by
        funext x
        rcases le_total 0 (g x) with h | h
        · rw [max_eq_right h, abs_of_nonneg h]; ring
        · rw [max_eq_left h, abs_of_nonpos h]; ring
      rw [hmax]
      exact ((hcont.mono hsub).add (hcont.mono hsub).abs).div_const 2
    exact hcontmax.div continuousOn_id (fun x hx => (lt_of_lt_of_le hu0 hx.1).ne')
  have hne : ∀ i : ℕ, i < K →
      ⌈Y ^ (16 / 135 + (i : ℝ) * ((89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)))⌉₊
        ≤ ⌊Y ^ (16 / 135 + ((i : ℝ) + 1) * ((89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ)))⌋₊ := by
    intro i _
    exact mesh_cond (a := 16 / 135) (W := (89 / 462 - 0.00000001 - 16 / 135) / (K : ℝ))
      (w0 := (89 / 462 - 0.00000001 - 16 / 135) / ((K : ℝ) ^ 2)) hY
      (div_nonneg (le_of_lt hd) (le_of_lt hKpos))
      (div_nonneg (le_of_lt hd) (by positivity))
      (by
        rw [div_le_div_iff₀ (by positivity) hKpos]
        nlinarith [hd, hKpos, hK2']) hstep i
  -- the staircase
  have hstair := prime_sum_block_le (Y := Y) (K := K) (μ := 89 / 462 - 0.00000001) hY
    (by omega) hab le_rfl hbig Phi hmono hnn hint hne
  -- the integral of `φ₃`
  have hgval : (∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001), g u / u)
      = (1 / 2) * ((∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001), Real.log (u / (16 / 135)) ^ 2 / u)
          - (∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001),
              Real.log (((71 / 135 - u) / 2) / (16 / 135)) ^ 2 / u)) := by
    have h1 : IntervalIntegrable (fun u : ℝ => Real.log (u / (16 / 135)) ^ 2 / u)
        MeasureTheory.volume (71 / 405) (89 / 462 - 0.00000001) := by
      apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      refine (ContinuousOn.log (by fun_prop) ?_).pow 2 |>.div continuousOn_id ?_
      · intro x hx
        have hx0 : (0 : ℝ) < x := by linarith [hx.1]
        exact div_ne_zero hx0.ne' (by norm_num)
      · intro x hx
        exact (by linarith [hx.1] : (0 : ℝ) < x).ne'
    have h2 : IntervalIntegrable (fun u : ℝ => Real.log (((71 / 135 - u) / 2) / (16 / 135)) ^ 2 / u)
        MeasureTheory.volume (71 / 405) (89 / 462 - 0.00000001) := by
      apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
      refine (ContinuousOn.log (by fun_prop) ?_).pow 2 |>.div continuousOn_id ?_
      · intro x hx
        exact (div_pos (by linarith [hx.2]) (by norm_num)).ne'
      · intro x hx
        exact (by linarith [hx.1] : (0 : ℝ) < x).ne'
    have hcongr : (∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001), g u / u)
        = ∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001),
            (1 / 2) * (Real.log (u / (16 / 135)) ^ 2 / u
              - Real.log (((71 / 135 - u) / 2) / (16 / 135)) ^ 2 / u) := by
      apply intervalIntegral.integral_congr
      intro u _
      simp only [hg]
      field_simp
      try ring
    rw [hcongr, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub h1 h2]
  have hPhiInt : (∫ u in (16 / 135)..(89 / 462 - 0.00000001), Phi u / u)
      = (1 / 2) * ((∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001), Real.log (u / (16 / 135)) ^ 2 / u)
          - (∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001),
              Real.log (((71 / 135 - u) / 2) / (16 / 135)) ^ 2 / u)) := by
    have hsplit : (∫ u in (16 / 135)..(89 / 462 - 0.00000001), Phi u / u)
        = (∫ u in (16 / 135)..(71 / 405 : ℝ), Phi u / u)
          + (∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001), Phi u / u) :=
      (integral_add_adjacent_intervals (hint (16 / 135) (71 / 405) le_rfl (by norm_num)
        (by norm_num)) (hint (71 / 405) (89 / 462 - 0.00000001) (by norm_num) (by norm_num) le_rfl)).symm
    have hzero : (∫ u in (16 / 135)..(71 / 405 : ℝ), Phi u / u) = 0 := by
      have h0 : ∀ u ∈ Set.uIcc (16 / 135) (71 / 405 : ℝ), Phi u / u = 0 := by
        intro u hu
        rw [Set.uIcc_of_le (by norm_num)] at hu
        have hg0 : g u ≤ 0 := by
          have hL : Real.log (u / (16 / 135)) ≤ Real.log (((71 / 135 - u) / 2) / (16 / 135)) := by
            have hu0 : (0 : ℝ) < u := by linarith [hu.1]
            apply Real.log_le_log (div_pos hu0 (by norm_num))
            apply div_le_div_of_nonneg_right _ (le_of_lt ha)
            linarith [hu.2]
          have hL0 : 0 ≤ Real.log (u / (16 / 135)) := Real.log_nonneg (by
            rw [le_div_iff₀ ha]; linarith [hu.1])
          have h1 : Real.log (u / (16 / 135)) ^ 2
              ≤ Real.log (((71 / 135 - u) / 2) / (16 / 135)) ^ 2 :=
            pow_le_pow_left₀ hL0 hL 2
          simp only [hg]
          linarith
        have : Phi u = 0 := by
          simp only [hPhi]
          exact max_eq_left hg0
        rw [this]
        ring
      rw [intervalIntegral.integral_congr h0, intervalIntegral.integral_zero]
    have hpos : (∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001), Phi u / u)
        = (∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001), g u / u) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le (by norm_num)] at hu
      have hg0 : 0 ≤ g u := by
        have hL : Real.log (((71 / 135 - u) / 2) / (16 / 135)) ≤ Real.log (u / (16 / 135)) := by
          have hbn : (89 / 462 - 0.00000001 : ℝ) < 71 / 135 := by norm_num
          have hnum2 : (0 : ℝ) < 71 / 135 - u := by linarith [hu.2, hbn]
          have hu0 : (0 : ℝ) < (71 / 135 - u) / 2 := by linarith
          apply Real.log_le_log (div_pos hu0 (by norm_num))
          apply div_le_div_of_nonneg_right _ (le_of_lt ha)
          linarith [hu.1]
        have hL0 : 0 ≤ Real.log (((71 / 135 - u) / 2) / (16 / 135)) := by
          apply Real.log_nonneg
          rw [le_div_iff₀ ha]
          linarith [hu.2]
        have h1 : Real.log (((71 / 135 - u) / 2) / (16 / 135)) ^ 2
            ≤ Real.log (u / (16 / 135)) ^ 2 := pow_le_pow_left₀ hL0 hL 2
        simp only [hg]
        linarith
      simp only [hPhi, max_eq_right hg0]
    rw [hsplit, hzero, zero_add, hpos, hgval]
  rw [hPhiInt] at hstair
  have hb : Phi (89 / 462 - 0.00000001)
      = max 0 ((1 / 2) * (Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 2
            - Real.log (((71 / 135 - (89 / 462 - 0.00000001 : ℝ)) / 2) / (16 / 135)) ^ 2)) := by
    simp only [hPhi, hg]
  rw [hb] at hstair
  rw [← he] at hstair
  simpa only [hPhi, hg] using hstair


open Real Finset intervalIntegral
open Decomp578c Decomp578d
open LeanLab.PNTSieve.Mertens
open LeanLab.Languasco2004.Decomp578d.WIP.LeanLab.Languasco2004.Decomp578d
open LeanLab.Languasco2004.Numeric565
noncomputable section

/-- The `if`-shape of the upper-branch model weight agrees with the `φ₃` staircase weight
`max 0 ((1/2)(log(x/a)^2 - log(cap(x)/a)^2))` used by `upper_stair_le`. -/
private theorem phi_glue {x : ℝ} (hx1 : 16 / 135 ≤ x) (hx2 : x ≤ 89 / 462 - 0.00000001) :
    (if x ≤ 71 / 405 then (0 : ℝ)
      else (1 / 2) * (Real.log (x / (16 / 135)) ^ 2
        - Real.log (((71 / 135 - x) / 2) / (16 / 135)) ^ 2))
      = max 0 ((1 / 2) * (Real.log (x / (16 / 135)) ^ 2
        - Real.log (((71 / 135 - x) / 2) / (16 / 135)) ^ 2)) := by
  have ha : (0 : ℝ) < 16 / 135 := by norm_num
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx1
  have hcap0 : 0 < (71 / 135 - x) / 2 := by linarith
  have hcapA : 16 / 135 ≤ (71 / 135 - x) / 2 := by linarith
  have hLx0 : 0 ≤ Real.log (x / (16 / 135)) :=
    Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith)
  have hLc0 : 0 ≤ Real.log (((71 / 135 - x) / 2) / (16 / 135)) :=
    Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith)
  by_cases h : x ≤ 71 / 405
  · have hxc : x ≤ (71 / 135 - x) / 2 := by linarith
    have hle : Real.log (x / (16 / 135)) ≤ Real.log (((71 / 135 - x) / 2) / (16 / 135)) :=
      Real.log_le_log (div_pos hx0 ha) (div_le_div_of_nonneg_right hxc ha.le)
    have hsq : Real.log (x / (16 / 135)) ^ 2 ≤ Real.log (((71 / 135 - x) / 2) / (16 / 135)) ^ 2 :=
      pow_le_pow_left₀ hLx0 hle 2
    rw [if_pos h, max_eq_left (by linarith)]
  · have hxc : (71 / 135 - x) / 2 ≤ x := by linarith
    have hle : Real.log (((71 / 135 - x) / 2) / (16 / 135)) ≤ Real.log (x / (16 / 135)) :=
      Real.log_le_log (div_pos hcap0 ha) (div_le_div_of_nonneg_right hxc ha.le)
    have hsq : Real.log (((71 / 135 - x) / 2) / (16 / 135)) ^ 2 ≤ Real.log (x / (16 / 135)) ^ 2 :=
      pow_le_pow_left₀ hLc0 hle 2
    rw [if_neg h, max_eq_right (by linarith)]



/-- `upper_point_le` with the model's `if`-weight replaced by the staircase weight. -/
private theorem upper_point_phi_le {Y : ℝ} {n p K : ℕ} {e : ℝ} (hY : 1 < Y) (hK2 : 2 ≤ K)
    (hbig : 2 * Real.log 2 ≤ (16 / 135) * Real.log Y)
    (he : e = (89 / 462 - 0.00000001 - 16 / 135) / ((16 / 135) * (K : ℝ))
            + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)))
    (he1 : e ≤ 1)
    (hstep : 2 ≤ Y ^ (16 / 135 : ℝ) *
      (Y ^ ((89 / 462 - 0.00000001 - 16 / 135) / ((K : ℝ) ^ 2)) - 1))
    (hn : 2 * Y ≤ (n : ℝ))
    (hp : p.Prime) (hpa : Y ^ (16 / 135 : ℝ) < (p : ℝ))
    (hpb : (p : ℝ) ≤ Y ^ (89 / 462 - 0.00000001 : ℝ)) :
    (∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
        Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)),
        (if (p : ℝ) * (q : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0
          else (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y))))
      ≤ max 0 ((1 / 2) * (Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) ^ 2
            - Real.log (((71 / 135 - Real.log (p : ℝ) / Real.log Y) / 2) / (16 / 135)) ^ 2))
        + 10 * e := by
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have h1 := upper_point_le (Y := Y) (n := n) (p := p) (K := K) (e := e)
    hY hK2 hbig he he1 hstep hn hp hpa hpb
  have hx1 : 16 / 135 ≤ Real.log (p : ℝ) / Real.log Y := by
    have h2 : Real.log (Y ^ (16 / 135 : ℝ)) < Real.log (p : ℝ) :=
      Real.log_lt_log (Real.rpow_pos_of_pos hY0 _) hpa
    rw [Real.log_rpow hY0] at h2
    rw [le_div_iff₀ hlogY]
    linarith
  have hx2 : Real.log (p : ℝ) / Real.log Y ≤ 89 / 462 - 0.00000001 := by
    have h2 : Real.log (p : ℝ) ≤ Real.log (Y ^ (89 / 462 - 0.00000001 : ℝ)) :=
      Real.log_le_log hp0 hpb
    rw [Real.log_rpow hY0] at h2
    rw [div_le_iff₀ hlogY]
    linarith
  have hiff : (p : ℝ) ≤ Y ^ (71 / 405 : ℝ) ↔ Real.log (p : ℝ) / Real.log Y ≤ 71 / 405 := by
    have hA : Real.log (p : ℝ) / Real.log Y ≤ 71 / 405
        ↔ Real.log (p : ℝ) ≤ (71 / 405) * Real.log Y := by
      rw [div_le_iff₀ hlogY]
    have hB : (p : ℝ) ≤ Y ^ (71 / 405 : ℝ)
        ↔ Real.log (p : ℝ) ≤ (71 / 405) * Real.log Y := by
      rw [← Real.log_le_log_iff hp0 (Real.rpow_pos_of_pos hY0 _), Real.log_rpow hY0]
    exact hB.trans hA.symm
  have hx := phi_glue hx1 hx2
  have hkey : (if (p : ℝ) ≤ Y ^ (71 / 405 : ℝ) then (0 : ℝ)
      else (1 / 2) * (Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) ^ 2
        - Real.log (((71 / 135 - Real.log (p : ℝ) / Real.log Y) / 2) / (16 / 135)) ^ 2))
      = max 0 ((1 / 2) * (Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) ^ 2
        - Real.log (((71 / 135 - Real.log (p : ℝ) / Real.log Y) / 2) / (16 / 135)) ^ 2)) := by
    by_cases h : (p : ℝ) ≤ Y ^ (71 / 405 : ℝ)
    · rw [if_pos h, ← hx, if_pos (hiff.mp h)]
    · rw [if_neg h, ← hx, if_neg (mt hiff.mpr h)]
  rw [hkey] at h1
  exact h1


/-- The upper branch: the per-prime bound `upper_point_phi_le` summed against `upper_stair_le`. -/
private theorem pair_upper_le {Y : ℝ} {n K : ℕ} {e S : ℝ} (hY : 1 < Y) (hK2 : 2 ≤ K)
    (hbig : 2 * Real.log 2 ≤ (16 / 135) * Real.log Y)
    (he : e = (89 / 462 - 0.00000001 - 16 / 135) / ((16 / 135) * (K : ℝ))
            + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)))
    (he1 : e ≤ 1)
    (hstep : 2 ≤ Y ^ (16 / 135 : ℝ) *
      (Y ^ ((89 / 462 - 0.00000001 - 16 / 135) / ((K : ℝ) ^ 2)) - 1))
    (hn : 2 * Y ≤ (n : ℝ))
    (hS : (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
            Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤ S)
    (hS0 : 0 ≤ S) :
    (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ) *
          (∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
              Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)),
            (if (p : ℝ) * (q : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0
              else (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y)))))
      ≤ (1 / 2) * ((∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001 : ℝ),
            Real.log (u / (16 / 135)) ^ 2 / u)
          - (∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001 : ℝ),
            Real.log (((71 / 135 - u) / 2) / (16 / 135)) ^ 2 / u))
        + (max 0 ((1 / 2) * (Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 2
              - Real.log (((71 / 135 - (89 / 462 - 0.00000001 : ℝ)) / 2) / (16 / 135)) ^ 2))) * e
        + 10 * e * S := by
  classical
  have hY0 : (0 : ℝ) < Y := by linarith
  have ha0 : (0 : ℝ) < Y ^ (16 / 135 : ℝ) := Real.rpow_pos_of_pos hY0 _
  have hb0 : (0 : ℝ) < Y ^ (89 / 462 - 0.00000001 : ℝ) := Real.rpow_pos_of_pos hY0 _
  set W : Finset ℕ :=
    (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter Nat.Prime with hW
  have hper : ∀ p ∈ W, (1 : ℝ) / (p : ℝ) *
      (∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
          Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)),
        (if (p : ℝ) * (q : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0
          else (1 : ℝ) / (q : ℝ) * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y))))
      ≤ (1 : ℝ) / (p : ℝ) *
        (max 0 ((1 / 2) * (Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) ^ 2
            - Real.log (((71 / 135 - Real.log (p : ℝ) / Real.log Y) / 2) / (16 / 135)) ^ 2))
          + 10 * e) := by
    intro p hp
    have hmem := Finset.mem_filter.mp hp
    have hpp : p.Prime := hmem.2
    have hIoc := Finset.mem_Ioc.mp hmem.1
    have hple : ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) ≤ Y ^ (16 / 135 : ℝ) := Nat.floor_le ha0.le
    have hpa : Y ^ (16 / 135 : ℝ) < (p : ℝ) := by
      have h2 : ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by
        have h2' : ⌊Y ^ (16 / 135 : ℝ)⌋₊ + 1 ≤ p := hIoc.1
        exact_mod_cast h2'
      have h3 : Y ^ (16 / 135 : ℝ) < ((⌊Y ^ (16 / 135 : ℝ)⌋₊ : ℕ) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      linarith
    have hpb : (p : ℝ) ≤ Y ^ (89 / 462 - 0.00000001 : ℝ) :=
      le_trans (by exact_mod_cast hIoc.2) (Nat.floor_le hb0.le)
    have h := upper_point_phi_le (Y := Y) (n := n) (p := p) (K := K) (e := e)
      hY hK2 hbig he he1 hstep hn hpp hpa hpb
    exact mul_le_mul_of_nonneg_left h (by positivity)
  refine le_trans (Finset.sum_le_sum hper) ?_
  have hsplit : (∑ p ∈ W, (1 : ℝ) / (p : ℝ) *
      (max 0 ((1 / 2) * (Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) ^ 2
          - Real.log (((71 / 135 - Real.log (p : ℝ) / Real.log Y) / 2) / (16 / 135)) ^ 2))
        + 10 * e))
      = (∑ p ∈ W, (1 : ℝ) / (p : ℝ) *
          max 0 ((1 / 2) * (Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) ^ 2
            - Real.log (((71 / 135 - Real.log (p : ℝ) / Real.log Y) / 2) / (16 / 135)) ^ 2)))
        + (∑ p ∈ W, (1 : ℝ) / (p : ℝ)) * (10 * e) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
  rw [hsplit]
  have hstair := upper_stair_le (Y := Y) (K := K) (e := e) hY hK2 hbig he hstep
  have hWle : (∑ p ∈ W, (1 : ℝ) / (p : ℝ)) ≤ S := by rw [hW]; exact hS
  have hKp : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have he0 : 0 ≤ e := by
    rw [he]
    have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlogY' : (0 : ℝ) < Real.log Y := Real.log_pos hY
    apply add_nonneg
    · apply div_nonneg (by norm_num) (by positivity)
    · apply mul_nonneg (by positivity)
      exact div_nonneg (by positivity) (by positivity)
  have h1 : (∑ p ∈ W, (1 : ℝ) / (p : ℝ)) * (10 * e) ≤ S * (10 * e) :=
    mul_le_mul_of_nonneg_right hWle (by positivity)
  have h2 : (∑ p ∈ W, (1 : ℝ) / (p : ℝ) *
          max 0 ((1 / 2) * (Real.log (Real.log (p : ℝ) / Real.log Y / (16 / 135)) ^ 2
            - Real.log (((71 / 135 - Real.log (p : ℝ) / Real.log Y) / 2) / (16 / 135)) ^ 2)))
      ≤ (1 / 2) * ((∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001 : ℝ),
            Real.log (u / (16 / 135)) ^ 2 / u)
          - (∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001 : ℝ),
            Real.log (((71 / 135 - u) / 2) / (16 / 135)) ^ 2 / u))
        + (max 0 ((1 / 2) * (Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 2
              - Real.log (((71 / 135 - (89 / 462 - 0.00000001 : ℝ)) / 2) / (16 / 135)) ^ 2))) * e := by
    rw [hW]
    exact hstair
  nlinarith [h1, h2]


/-- Integrability of `log(u/a)^2/u` on a positive interval. -/
private theorem logsq_intable {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    IntervalIntegrable (fun x : ℝ => Real.log (x / (16 / 135)) ^ 2 / x)
      MeasureTheory.volume u v := by
  apply ContinuousOn.intervalIntegrable_of_Icc huv
  refine (ContinuousOn.log (by fun_prop) ?_).pow 2 |>.div continuousOn_id ?_
  · intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hu hx.1
    exact div_ne_zero hx0.ne' (by norm_num)
  · intro x hx
    exact (lt_of_lt_of_le hu hx.1).ne'


/-- The limit constant compared with `tripleOne + tripleTwo + tripleThree`, in the shape the
model bound produces: `0.5617` times the full band integral plus `0.0027` times the
upper-branch staircase integral. -/
private theorem const_le' :
    (135 / 16) * (0.5617 * (Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 3 / 6)
        + 0.0027 * ((1 / 2) * ((∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001 : ℝ),
              Real.log (u / (16 / 135)) ^ 2 / u)
            - (∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001 : ℝ),
              Real.log (((71 / 135 - u) / 2) / (16 / 135)) ^ 2 / u))))
      ≤ tripleOne + tripleTwo + tripleThree := by
  have harg2 : ∀ u : ℝ, ((71 / 135 - u) / 2) / (16 / 135) = (71 / 135 - u) / (2 * (16 / 135)) := by
    intro u
    field_simp
  have hI2 : (∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001 : ℝ),
        Real.log (((71 / 135 - u) / 2) / (16 / 135)) ^ 2 / u)
      = (∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001 : ℝ),
        Real.log ((71 / 135 - u) / (2 * (16 / 135))) ^ 2 / u) := by
    apply intervalIntegral.integral_congr
    intro u _
    show Real.log (((71 / 135 - u) / 2) / (16 / 135)) ^ 2 / u
        = Real.log ((71 / 135 - u) / (2 * (16 / 135))) ^ 2 / u
    rw [harg2 u]
  rw [hI2]
  set J1 : ℝ := ∫ u in (16 / 135 : ℝ)..(71 / 405 : ℝ), Real.log (u / (16 / 135)) ^ 2 / u with hJ1
  set J2 : ℝ := ∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001 : ℝ),
    Real.log ((71 / 135 - u) / (2 * (16 / 135))) ^ 2 / u with hJ2
  set J3 : ℝ := ∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001 : ℝ),
    Real.log (u / (16 / 135)) ^ 2 / u with hJ3
  have hT := const_le
  have hTL : (135 / 16) * (0.5617 *
        ((1 / 2) * (∫ u in (16 / 135 : ℝ)..(71 / 405 : ℝ), Real.log (u / (16 / 135)) ^ 2 / u)
       + (1 / 2) * (∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001 : ℝ),
            Real.log ((71 / 135 - u) / (2 * (16 / 135))) ^ 2 / u))
      + 0.5644 *
        ((1 / 2) * (∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001 : ℝ),
            Real.log (u / (16 / 135)) ^ 2 / u)
       - (1 / 2) * (∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001 : ℝ),
            Real.log ((71 / 135 - u) / (2 * (16 / 135))) ^ 2 / u)))
      = (135 / 16) * (0.5617 * ((1 / 2) * J1 + (1 / 2) * J2)
        + 0.5644 * ((1 / 2) * J3 - (1 / 2) * J2)) := by
    rw [← hJ1, ← hJ2, ← hJ3]
  rw [hTL] at hT
  have hsplit : (∫ u in (16 / 135 : ℝ)..(89 / 462 - 0.00000001 : ℝ),
      Real.log (u / (16 / 135)) ^ 2 / u) = J1 + J3 := by
    rw [hJ1, hJ3]
    exact (integral_add_adjacent_intervals
      (logsq_intable (by norm_num) (by norm_num))
      (logsq_intable (by norm_num) (by norm_num))).symm
  have hL6 : Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 3 / 6
      = (1 / 2) * J1 + (1 / 2) * J3 := by
    have h0 := integral_logsq_ratio (16 / 135) (89 / 462 - 0.00000001) (by norm_num) (by norm_num)
    rw [hsplit] at h0
    linarith
  rw [hL6]
  have heq : (135 / 16) * (0.5617 * ((1 / 2) * J1 + (1 / 2) * J3)
        + 0.0027 * ((1 / 2) * (J3 - J2)))
      = (135 / 16) * (0.5617 * ((1 / 2) * J1 + (1 / 2) * J2)
        + 0.5644 * ((1 / 2) * J3 - (1 / 2) * J2)) := by ring
  rw [heq]
  exact hT


/-- `log (b/a) ≤ 1` for the model band. -/
private theorem bandL_le_one : Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ≤ 1 := by
  have hx0 : (0 : ℝ) < (89 / 462 - 0.00000001) / (16 / 135) := by norm_num
  have h := Real.log_le_sub_one_of_pos hx0
  have h2 : (89 / 462 - 0.00000001 : ℝ) / (16 / 135) ≤ 2 := by norm_num
  linarith


/-- `log (b/a) ≥ 0` for the model band. -/
private theorem bandL_nonneg : 0 ≤ Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) := by
  apply Real.log_nonneg
  norm_num


/-- The staircase weight at the top of the band is at most `1`. -/
private theorem bandPhi_le_one :
    max 0 ((1 / 2) * (Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 2
        - Real.log (((71 / 135 - ((89 / 462 - 0.00000001 : ℝ))) / 2) / (16 / 135)) ^ 2)) ≤ 1 := by
  have h0 := bandL_nonneg
  have h1 := bandL_le_one
  have hsq : Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 2 ≤ 1 := by nlinarith
  have hcap : 0 ≤ Real.log (((71 / 135 - ((89 / 462 - 0.00000001 : ℝ))) / 2) / (16 / 135)) ^ 2 :=
    sq_nonneg _
  have : (1 / 2) * (Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 2
      - Real.log (((71 / 135 - ((89 / 462 - 0.00000001 : ℝ))) / 2) / (16 / 135)) ^ 2) ≤ 1 := by
    nlinarith
  exact max_le (by norm_num) this


/-- **The model bound.**  The triple prime model is at most the limiting constant plus the
explicit error budget `errF`, `errG`. -/
private theorem model_bound {Y : ℝ} {n K : ℕ} {e S : ℝ} (hY : 1 < Y) (hK2 : 2 ≤ K)
    (hbig : 2 * Real.log 2 ≤ (16 / 135) * Real.log Y)
    (he : e = (89 / 462 - 0.00000001 - 16 / 135) / ((16 / 135) * (K : ℝ))
            + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)))
    (he1 : e ≤ 1)
    (hstep : 2 ≤ Y ^ (16 / 135 : ℝ) *
      (Y ^ ((89 / 462 - 0.00000001 - 16 / 135) / ((K : ℝ) ^ 2)) - 1))
    (hn : 2 * Y ≤ (n : ℝ))
    (hS : (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
            Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤ S)
    (hSicc : (∑ p ∈ (Icc ⌈Y ^ (16 / 135 : ℝ)⌉₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
            Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤ S)
    (hS0 : 0 ≤ S) :
    triplePrimeModel Y n ≤
      (135 / 16) * (0.5617 * (Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 3 / 6)
          + 0.0027 * ((1 / 2) * ((∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001 : ℝ),
                Real.log (u / (16 / 135)) ^ 2 / u)
              - (∫ u in (71 / 405 : ℝ)..(89 / 462 - 0.00000001 : ℝ),
                Real.log (((71 / 135 - u) / 2) / (16 / 135)) ^ 2 / u))))
        + (135 / 16) * (0.5617 *
            (46 * Real.log 2 / ((16 / 135) * Real.log Y) * (S * S)
              + e * Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 2
              + Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) * e ^ 2
              + 3 * e ^ 2 * S)
          + 0.0027 *
            (46 * Real.log 2 / ((16 / 135) * Real.log Y) * (S * S)
              + (max 0 ((1 / 2) * (Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 2
                  - Real.log (((71 / 135 - ((89 / 462 - 0.00000001 : ℝ))) / 2) / (16 / 135)) ^ 2))) * e
              + 10 * e * S)) := by
  classical
  have hY0 : (0 : ℝ) < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have ha : (0 : ℝ) < 16 / 135 := by norm_num
  have hα2 : 2 ≤ Y ^ (16 / 135 : ℝ) := by
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    have h2 : Real.log 2 ≤ Real.log (Y ^ (16 / 135 : ℝ)) := by
      rw [Real.log_rpow hY0]
      linarith
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log (Y ^ (16 / 135 : ℝ))) := Real.exp_le_exp.mpr h2
      _ = Y ^ (16 / 135 : ℝ) := Real.exp_log (Real.rpow_pos_of_pos hY0 _)
  have h1 := model_le_branch Y n
  have h2 := pair_sum_le_log (Y := Y) (n := n) (S := S) hY hα2 hbig hSicc hS0
  have h3 := pair_sum_le_log_upper (Y := Y) (n := n) (S := S) hY hα2 hbig hSicc hS0
  have h4 := pair_full_le (Y := Y) (n := n) (K := K) (e := e) (S := S) hY hK2 hbig he hstep hS hS0
  have h5 := pair_upper_le (Y := Y) (n := n) (K := K) (e := e) (S := S) hY hK2 hbig he he1 hstep hn hS hS0
  -- the `if`-sum of `pair_sum_le_log_upper` is the filtered upper-branch sum
  have h6 : (∑ pq ∈ Source565.pairDomain true Y n,
        if (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0 else
          (1 : ℝ) / ((pq.1 : ℝ) * (pq.2 : ℝ))
            * Real.log (Real.log (pq.2 : ℝ) / ((16 / 135) * Real.log Y)))
      ≤ ∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ) *
            (∑ q ∈ (range (n + 1)).filter (fun q : ℕ => q.Prime ∧
                Y ^ (16 / 135 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < (p : ℝ)),
              (if (p : ℝ) * (q : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ) then 0
                else (1 : ℝ) / (q : ℝ)
                  * Real.log (Real.log (q : ℝ) / ((16 / 135) * Real.log Y)))) := by
    refine le_trans ?_ (upper_pair_split_le (Y := Y) (n := n) hY)
    rw [Finset.sum_filter]
    apply le_of_eq
    refine Finset.sum_congr rfl (fun pq _ => ?_)
    by_cases h : (pq.1 : ℝ) * (pq.2 : ℝ) ^ 2 ≤ Y ^ (71 / 135 : ℝ)
    · simp [h]
    · simp [h]
  -- the exponents
  set L : ℝ := Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) with hL
  set PHI : ℝ := max 0 ((1 / 2) * (L ^ 2
      - Real.log (((71 / 135 - ((89 / 462 - 0.00000001 : ℝ))) / 2) / (16 / 135)) ^ 2)) with hPHI
  set E : ℝ := 46 * Real.log 2 / ((16 / 135) * Real.log Y) * (S * S) with hE
  have hL2 : e * (L ^ 2 + L * e) = e * L ^ 2 + L * e ^ 2 := by ring
  rw [hL2] at h4
  linarith [h1, h2, h3, h4, h5, h6]


/-- **The error budget.**  `errF` and `errG` together cost at most `1.72 (S+1) δ + 0.5645 E`. -/
private theorem err_step {e δ S E L PHI : ℝ} (he0 : 0 ≤ e) (heδ : e ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hS0 : 0 ≤ S) (hL0 : 0 ≤ L) (hL1 : L ≤ 1) (hPHI1 : PHI ≤ 1) (hE0 : 0 ≤ E) :
    (135 / 16) * (0.5617 * (E + e * L ^ 2 + L * e ^ 2 + 3 * e ^ 2 * S)
        + 0.0027 * (E + PHI * e + 10 * e * S))
      ≤ (135 / 16) * (1.72 * (S + 1) * δ + 0.5645 * E) := by
  have hLsq : L ^ 2 ≤ 1 := by nlinarith
  have he2 : e ^ 2 ≤ δ := by nlinarith
  have h1 : e * L ^ 2 ≤ δ := by
    calc e * L ^ 2 ≤ δ * 1 := mul_le_mul heδ hLsq (sq_nonneg L) (by linarith)
      _ = δ := by ring
  have h2 : L * e ^ 2 ≤ δ := by
    calc L * e ^ 2 ≤ 1 * δ := mul_le_mul hL1 he2 (sq_nonneg e) (by linarith)
      _ = δ := by ring
  have h3 : 3 * e ^ 2 * S ≤ 3 * δ * S := by nlinarith
  have h4 : PHI * e ≤ δ := by
    calc PHI * e ≤ 1 * δ := mul_le_mul hPHI1 heδ he0 (by linarith)
      _ = δ := by ring
  have h5 : 10 * e * S ≤ 10 * δ * S := by nlinarith
  nlinarith [h1, h2, h3, h4, h5, hS0, hδ1]


/-- **The numerical error budget.** -/
private theorem err_total {η δ S E logY : ℝ} (hη : 0 < η) (hδ : 400 * (S + 1) * δ ≤ η)
    (hS0 : 0 ≤ S) (hlogY : 0 < logY) (hbig : 4000 * S ^ 2 / η ≤ logY)
    (hE : E = 46 * Real.log 2 / ((16 / 135) * logY) * (S * S)) :
    (135 / 16) * (1.72 * (S + 1) * δ + 0.5645 * E) ≤ η := by
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h1 : (S + 1) * δ ≤ η / 400 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 400)]
    linarith
  have h2 : S ^ 2 / logY ≤ η / 4000 := by
    rw [div_le_iff₀ hlogY]
    have h3 : 4000 * S ^ 2 ≤ η * logY := by
      rw [div_le_iff₀ hη] at hbig
      linarith
    linarith
  have hA : 46 * Real.log 2 / ((16 / 135) * logY) ≤ 270 / logY := by
    rw [div_le_div_iff₀ (by positivity) hlogY]
    have h3 : 46 * Real.log 2 ≤ 270 * (16 / 135) := by nlinarith
    nlinarith
  have hE' : E ≤ 270 * (S ^ 2 / logY) := by
    rw [hE]
    have h3 := mul_le_mul_of_nonneg_right hA (by positivity : (0 : ℝ) ≤ S * S)
    have h4 : 270 / logY * (S * S) = 270 * (S ^ 2 / logY) := by
      have hl : logY ≠ 0 := hlogY.ne'
      field_simp
    rw [h4] at h3
    exact h3
  have h5 : 0.5645 * E ≤ 0.5645 * (270 * (η / 4000)) := by
    have h6 : (0 : ℝ) ≤ S ^ 2 / logY := by positivity
    linarith [hE', h2]
  have h7 : 1.72 * (S + 1) * δ ≤ 1.72 * (η / 400) := by nlinarith [h1]
  nlinarith [h5, h7, hη]


set_option maxHeartbeats 4000000 in
/-- **The leaf.**  `triple_prime_sum_upper` for the model triple prime sum. -/
private theorem triple_prime_sum_upper_holds :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∀ n : ℕ, 2 * Y ≤ (n : ℝ) →
        triplePrimeModel Y n ≤ tripleOne + tripleTwo + tripleThree + η := by
  intro η hη
  set S : ℝ := 2 * Real.log 4 * (1 / Real.log 2 + 1) with hSdef
  have hS0 : 0 ≤ S := by rw [hSdef]; positivity
  have hS1 : (0 : ℝ) < S + 1 := by linarith
  set δ : ℝ := min 1 (η / (400 * (S + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ η / (400 * (S + 1)) := min_le_right _ _
  have hδle : 400 * (S + 1) * δ ≤ η := by
    have h := mul_le_mul_of_nonneg_left hδ2 (by positivity : (0 : ℝ) ≤ 400 * (S + 1))
    have h2 : 400 * (S + 1) * (η / (400 * (S + 1))) = η := by
      have hS1' : (400 : ℝ) * (S + 1) ≠ 0 := by positivity
      field_simp
    linarith [h, h2]
  set D : ℝ := 89 / 462 - 0.00000001 - 16 / 135 with hDdef
  have hD0 : 0 < D := by rw [hDdef]; norm_num
  set K : ℕ := ⌈2 * D / ((16 / 135) * δ)⌉₊ + 2 with hKdef
  have hK2 : 2 ≤ K := by rw [hKdef]; exact Nat.le_add_left 2 _
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    have h : 0 < K := by omega
    exact_mod_cast h
  have hKge : 2 * D / ((16 / 135) * δ) ≤ (K : ℝ) := by
    rw [hKdef]
    have hc : 2 * D / ((16 / 135) * δ) ≤ ((⌈2 * D / ((16 / 135) * δ)⌉₊ : ℕ) : ℝ) :=
      Nat.le_ceil _
    push_cast
    linarith [hc]
  have hKD : D / ((16 / 135) * (K : ℝ)) ≤ δ / 2 := by
    have ha : (0 : ℝ) < 16 / 135 := by norm_num
    have haK : 2 * D / δ ≤ (16 / 135) * (K : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hKge ha.le
      have heq : (16 / 135) * (2 * D / ((16 / 135) * δ)) = 2 * D / δ := by
        field_simp
      linarith [h, heq]
    rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
    have haK' : 2 * D ≤ (16 / 135) * (K : ℝ) * δ := by
      have hm := mul_le_mul_of_nonneg_right haK (le_of_lt hδ0)
      have heq : 2 * D / δ * δ = 2 * D := by field_simp
      linarith [hm, heq]
    linarith [haK']
  set MT2 : ℝ := 2 * (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * δ)) with hMT2
  set MT3 : ℝ := (K : ℝ) ^ 2 * Real.log 2 / D with hMT3
  set MT4 : ℝ := Real.log 2 / (16 / 135) with hMT4
  set M : ℝ := max 12 (max (4000 * S ^ 2 / η) (max MT2 (max MT3 MT4))) with hMdef
  have hM1 : 4000 * S ^ 2 / η ≤ M := by
    rw [hMdef]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hM23 : max MT2 (max MT3 MT4) ≤ M := by
    rw [hMdef]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hM2 : MT2 ≤ M := le_trans (le_max_left _ _) hM23
  have hM3 : MT3 ≤ M := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hM23)
  have hM4 : MT4 ≤ M := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hM23)
  refine ⟨Real.exp M, ?_⟩
  intro Y hYle n hn
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le (Real.exp_pos M) hYle
  have hY1 : 1 < Y := by
    have h12 : (12 : ℝ) ≤ M := by rw [hMdef]; exact le_max_left _ _
    have h1 : (1 : ℝ) < Real.exp M := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
    exact lt_of_lt_of_le h1 hYle
  have hlogY : M ≤ Real.log Y := by
    have h := Real.log_le_log (Real.exp_pos M) hYle
    rwa [Real.log_exp] at h
  have hlogY0 : 0 < Real.log Y := Real.log_pos hY1
  set e : ℝ := D / ((16 / 135) * (K : ℝ))
      + (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)) with hedef
  have heKterm : (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y)) ≤ δ / 2 := by
    have hd : 0 < (16 / 135) * δ := by positivity
    have h1 : MT2 ≤ Real.log Y := le_trans hM2 hlogY
    have h1' : 2 * (K : ℝ) * (42 * Real.log 2) ≤ δ * ((16 / 135) * Real.log Y) := by
      have hm := mul_le_mul_of_nonneg_right h1 hd.le
      have heq : 2 * (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * δ)) * ((16 / 135) * δ)
          = 2 * (K : ℝ) * (42 * Real.log 2) := by
        field_simp
      rw [heq] at hm
      calc 2 * (K : ℝ) * (42 * Real.log 2) ≤ Real.log Y * ((16 / 135) * δ) := hm
        _ = δ * ((16 / 135) * Real.log Y) := by ring
    have hgeq : (K : ℝ) * (42 * Real.log 2 / ((16 / 135) * Real.log Y))
        = (2 * (K : ℝ) * (42 * Real.log 2)) / (2 * ((16 / 135) * Real.log Y)) := by
      field_simp
    rw [hgeq, div_le_iff₀ (by positivity)]
    nlinarith [h1']
  have he_le : e ≤ δ := by rw [hedef]; linarith
  have he1 : e ≤ 1 := le_trans he_le hδ1
  have he0 : 0 ≤ e := by rw [hedef]; positivity
  have hbigY : 2 * Real.log 2 ≤ (16 / 135) * Real.log Y := by
    have h12 : (12 : ℝ) ≤ Real.log Y := le_trans (by rw [hMdef]; exact le_max_left _ _) hlogY
    have hlog2 : Real.log 2 ≤ 0.7 := le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num))
    linarith
  have hstepY : 2 ≤ Y ^ (16 / 135 : ℝ) * (Y ^ (D / ((K : ℝ) ^ 2)) - 1) := by
    have hYa : 2 ≤ Y ^ (16 / 135 : ℝ) := by
      have hM4' : MT4 ≤ Real.log Y := le_trans hM4 hlogY
      have h1 : Real.log 2 ≤ (16 / 135) * Real.log Y := by
        rw [hMT4] at hM4'
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 16 / 135)] at hM4'
        linarith
      calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
        _ ≤ Real.exp ((16 / 135) * Real.log Y) := Real.exp_le_exp.mpr h1
        _ = Real.exp (Real.log (Y ^ (16 / 135 : ℝ))) := by rw [Real.log_rpow hY0]
        _ = Y ^ (16 / 135 : ℝ) := Real.exp_log (Real.rpow_pos_of_pos hY0 _)
    have hYW : 2 ≤ Y ^ (D / ((K : ℝ) ^ 2)) := by
      have hM3' : MT3 ≤ Real.log Y := le_trans hM3 hlogY
      have h1 : Real.log 2 ≤ (D / ((K : ℝ) ^ 2)) * Real.log Y := by
        rw [hMT3] at hM3'
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < (K : ℝ) ^ 2)]
        have hm := mul_le_mul_of_nonneg_left hM3' (le_of_lt hD0)
        have heq : D * ((K : ℝ) ^ 2 * Real.log 2 / D) = (K : ℝ) ^ 2 * Real.log 2 := by
          field_simp
        rw [heq] at hm
        linarith [hm]
      calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
        _ ≤ Real.exp ((D / ((K : ℝ) ^ 2)) * Real.log Y) := Real.exp_le_exp.mpr h1
        _ = Real.exp (Real.log (Y ^ (D / ((K : ℝ) ^ 2)))) := by rw [Real.log_rpow hY0]
        _ = Y ^ (D / ((K : ℝ) ^ 2)) := Real.exp_log (Real.rpow_pos_of_pos hY0 _)
    have hW1 : 1 ≤ Y ^ (D / ((K : ℝ) ^ 2)) - 1 := by linarith
    calc (2 : ℝ) = 2 * 1 := by ring
      _ ≤ Y ^ (16 / 135 : ℝ) * (Y ^ (D / ((K : ℝ) ^ 2)) - 1) :=
          mul_le_mul hYa hW1 (by norm_num) (by linarith)
  have hα1 : 1 < Y ^ (16 / 135 : ℝ) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (16 / 135 : ℝ) := (Real.one_rpow _).symm
      _ < Y ^ (16 / 135 : ℝ) := Real.rpow_lt_rpow (by norm_num) hY1 (by norm_num)
  have hαβ : Y ^ (16 / 135 : ℝ) ≤ Y ^ (89 / 462 - 0.00000001 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hY1.le (by norm_num)
  have hlogα : 1 ≤ Real.log (Y ^ (16 / 135 : ℝ)) := by
    rw [Real.log_rpow hY0]
    have h12 : (12 : ℝ) ≤ Real.log Y := le_trans (by rw [hMdef]; exact le_max_left _ _) hlogY
    nlinarith
  have hrat : Real.log (Y ^ (89 / 462 - 0.00000001 : ℝ))
      ≤ 2 * Real.log (Y ^ (16 / 135 : ℝ)) := by
    rw [Real.log_rpow hY0, Real.log_rpow hY0]
    nlinarith [hlogY0]
  have hmain := sum_inv_primes_window_le (X := Y ^ (16 / 135 : ℝ))
    (Z := Y ^ (89 / 462 - 0.00000001 : ℝ)) hα1 hαβ hlogα hrat
  have hSicc : (∑ p ∈ (Icc ⌈Y ^ (16 / 135 : ℝ)⌉₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
        Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤ S := by
    rw [hSdef]
    exact hmain
  have hSw : (∑ p ∈ (Ioc ⌊Y ^ (16 / 135 : ℝ)⌋₊ ⌊Y ^ (89 / 462 - 0.00000001 : ℝ)⌋₊).filter
        Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤ S := by
    rw [hSdef]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => by positivity)) hmain
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hIoc := Finset.mem_Ioc.mp hp'.1
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hp'.2⟩
    · have h1 : ⌈Y ^ (16 / 135 : ℝ)⌉₊ ≤ ⌊Y ^ (16 / 135 : ℝ)⌋₊ + 1 :=
        Nat.ceil_le_floor_add_one _
      omega
    · exact hIoc.2
  have hL0 := bandL_nonneg
  have hL1 := bandL_le_one
  have hPHI1 := bandPhi_le_one
  have hE0 : (0 : ℝ) ≤ 46 * Real.log 2 / ((16 / 135) * Real.log Y) * (S * S) := by positivity
  have hmb := model_bound (Y := Y) (n := n) (K := K) (e := e) (S := S)
    hY1 hK2 hbigY hedef he1 hstepY hn hSw hSicc hS0
  have hc := const_le'
  have hes := err_step (e := e) (δ := δ) (S := S)
    (L := Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)))
    (PHI := max 0 ((1 / 2) * (Real.log ((89 / 462 - 0.00000001 : ℝ) / (16 / 135)) ^ 2
        - Real.log (((71 / 135 - ((89 / 462 - 0.00000001 : ℝ))) / 2) / (16 / 135)) ^ 2)))
    (E := 46 * Real.log 2 / ((16 / 135) * Real.log Y) * (S * S))
    he0 he_le hδ0.le hδ1 hS0 hL0 hL1 hPHI1 hE0
  have het := err_total (η := η) (δ := δ) (S := S)
    (E := 46 * Real.log 2 / ((16 / 135) * Real.log Y) * (S * S)) (logY := Real.log Y)
    hη hδle hS0 hlogY0 (le_trans hM1 hlogY) rfl
  linarith [hmb, hc, hes, het]



end
end
end WIP

/-- LEAF. Jia pages 284 and 285, the three triple prime sum integrals before display 64.
Only the weighted reciprocal prime sum is estimated. No rough integer sieve count remains.
Integral565 reduces the reciprocal inner integrals to the three Numeric565 integrals. -/
theorem triple_prime_sum_upper :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∀ n : ℕ, 2 * Y ≤ (n : ℝ) →
        triplePrimeModel Y n ≤ tripleOne + tripleTwo + tripleThree + η := by
  exact WIP.triple_prime_sum_upper_holds

/-- Page 284 support: the B triple mass has no dependence on the ambient prime location N. -/
theorem triple_model_independent (N Y : ℝ) (n : ℕ) (α z : ℝ) :
    tripleMass true true N Y n α z = tripleMass true true 0 Y n α z := by rfl

/-- Jia pages 284 and 285: the exact supplied type of the sealed model_triple_upper.
CONDITIONAL ON the two proper triple inputs and the three explicit Buchstab inputs.
The eventual model estimate is pointwise, so its exceptional set is empty. -/
theorem model_triple_upper_from_parts :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        (tripleOne + tripleTwo + tripleThree + 0.0000001) * scale N (localization N ε) n < modelTriple true N (localization N ε) n)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨Y1, h1⟩ := triple_rough_upper buchstab_solution lemma20_global_bounds
    lemma21_rough_asymptotic 0.00000005 (by norm_num)
  obtain ⟨Y2, h2⟩ := triple_prime_sum_upper 0.00000005 (by norm_num)
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro ε B hε he hB
  obtain ⟨N₀, hN₀⟩ := localization_model_domain ε (max Y1 Y2) hε he
  refine ⟨0, N₀, ?_⟩
  intro N hN
  have hd := hN₀ N hN
  have hY1 := (le_max_left Y1 Y2).trans hd.2.2.1
  have hY2 := (le_max_right Y1 Y2).trans hd.2.2.1
  have hempty : (window N ε).filter (fun n =>
      (tripleOne + tripleTwo + tripleThree + 0.0000001) * scale N (localization N ε) n <
        modelTriple true N (localization N ε) n) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro n hn hbad
    have hc := h2 _ hY2 n (hd.2.2.2 n hn)
    have hr := h1 _ hY1 n (hd.2.2.2 n hn)
    have hnorm := normalize_upper N (localization N ε)
      (triplePrimeModel (localization N ε) n + 0.00000005)
      (tripleMass true true 0 (localization N ε) n
        ((localization N ε) ^ (16 / 135 : ℝ)) ((localization N ε) ^ (16 / 135 : ℝ))) n hd.1 hr
    have hs := scale_nonneg n hd.1 hd.2.1
    have hcoef : triplePrimeModel (localization N ε) n + 0.00000005 ≤
        tripleOne + tripleTwo + tripleThree + 0.0000001 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hcoef hs
    rw [← triple_model_independent N] at hnorm
    change modelTriple true N (localization N ε) n ≤
      (triplePrimeModel (localization N ε) n + 0.00000005) * scale N (localization N ε) n at hnorm
    linarith
  simp only [hempty, card_empty, Nat.cast_zero, zero_mul, zero_div, le_refl]

#print axioms triplePrimeModel
#print axioms triple_rough_upper
#print axioms triple_prime_sum_upper
#print axioms triple_model_independent
#print axioms model_triple_upper_from_parts
end
end LeanLab.Languasco2004.Decomp578d
