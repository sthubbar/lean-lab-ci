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


/-- LEAF. Jia pages 284 and 285, the three triple prime sum integrals before display 64.
Only the weighted reciprocal prime sum is estimated. No rough integer sieve count remains.
Integral565 reduces the reciprocal inner integrals to the three Numeric565 integrals. -/
theorem triple_prime_sum_upper :
    ∀ η : ℝ, 0 < η → ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ∀ n : ℕ, 2 * Y ≤ (n : ℝ) →
        triplePrimeModel Y n ≤ tripleOne + tripleTwo + tripleThree + η := by sorry

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
