/-
Split of `bv_remainder` from `Decomp506b` into its proof steps. The three leaves are the
distribution input for squarefree moduli at level `Y ^ (1 / 9)`, the logarithmic size of
that modulus range, and the large-`X` regime of the parameters. The assembly
`bv_remainder_split` has no sorry of its own: it is bookkeeping, converting the
modulus-weighted discrepancy sum into the unweighted sum inside `remainder` and paying
one logarithmic factor for it.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp506b
import LeanLab.KumchevLiu2007.Decomp542a
import LeanLab.PNTPort.BV.FromSW
import LeanLab.PNTPort.PsiChi.SiegelWalfisz
import LeanLab.PNTPort.BVMax.Primes

namespace LeanLab.KumchevLiu2007.Task506b

open Real Complex MeasureTheory
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: The lab `BVPi` chain is unconditional and sorry-free. -/
theorem bvPi_unconditional : LeanLab.PNTPort.BVMax.BVPi :=
  LeanLab.PNTPort.BVMax.bvPi_of (LeanLab.PNTPort.BVMax.bvTheta_of
    (LeanLab.PNTPort.BVMax.bombieriVinogradovMax_of
      (LeanLab.PNTPort.BV.bombieriVinogradov_of_siegelWalfisz
        LeanLab.PNTPort.PsiChi.siegelWalfisz)))

lemma piAP_eq_primeAP (y : ℝ) (q a : ℕ) :
    LeanLab.PNTPort.BVMax.piAP y q a = Task542a.primeAP y q a := by
  have hset : (Finset.Icc 1 ⌊y⌋₊).filter (fun n : ℕ => n % q = a % q ∧ n.Prime)
      = (Finset.Icc 1 ⌊y⌋₊).filter (fun n : ℕ => n.Prime ∧ n % q = a % q) := by
    ext n
    simp only [Finset.mem_filter]
    tauto
  simp only [LeanLab.PNTPort.BVMax.piAP, LeanLab.PNTPort.BVMax.piN, Task542a.primeAP, hset]

/-- LEAF: `f t = 1/log t` is interval-integrable on every interval inside `[2, ∞)`. -/
lemma intervalIntegrable_one_div_log {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  have hcont : ContinuousOn Real.log (Set.Icc a b) := by
    refine continuousOn_log.mono ?_
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith [hx.1]
  exact ContinuousOn.div continuousOn_const hcont
    (fun t ht => ne_of_gt (Real.log_pos (by linarith [ht.1])))

/-- LEAF: On each unit interval the integral of `1/log` is trapped by the endpoint values. -/
lemma unit_interval_bounds (n : ℕ) (hn : 2 ≤ n) :
    1 / Real.log ((n : ℝ) + 1) ≤ ∫ t in (n : ℝ)..((n : ℝ) + 1), 1 / Real.log t ∧
    ∫ t in (n : ℝ)..((n : ℝ) + 1), 1 / Real.log t ≤ 1 / Real.log (n : ℝ) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · have h := intervalIntegral.integral_mono_on_of_le_Ioo (a := (n : ℝ)) (b := (n : ℝ) + 1)
      (f := fun _ : ℝ => 1 / Real.log ((n : ℝ) + 1)) (g := fun t : ℝ => 1 / Real.log t)
      (by linarith) intervalIntegrable_const
      (intervalIntegrable_one_div_log hn2 (by linarith)) (fun x hx => by
        have hx2 : x < (n : ℝ) + 1 := hx.2
        have hpos : 0 < Real.log x := Real.log_pos (by linarith [hx.1, hn2])
        have hlog : Real.log x ≤ Real.log ((n : ℝ) + 1) :=
          Real.log_le_log (by linarith [hx.1]) (le_of_lt hx2)
        exact one_div_le_one_div_of_le hpos hlog)
    simpa using h
  · have h := intervalIntegral.integral_mono_on_of_le_Ioo (a := (n : ℝ)) (b := (n : ℝ) + 1)
      (f := fun t : ℝ => 1 / Real.log t) (g := fun _ : ℝ => 1 / Real.log (n : ℝ))
      (by linarith) (intervalIntegrable_one_div_log hn2 (by linarith)) intervalIntegrable_const
      (fun x hx => by
        have hx1 : (n : ℝ) < x := hx.1
        have hpos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
        have hlog : Real.log (n : ℝ) ≤ Real.log x := Real.log_le_log (by linarith) (le_of_lt hx1)
        exact one_div_le_one_div_of_le hpos hlog)
    simpa using h

/-- LEAF: The integral is the sum of its unit pieces. -/
lemma integral_eq_sum_Ico (N : ℕ) (hN : 2 ≤ N) :
    ∫ t in (2 : ℝ)..(N : ℝ), 1 / Real.log t
      = ∑ n ∈ Finset.Ico 2 N, ∫ t in (n : ℝ)..((n : ℝ) + 1), 1 / Real.log t := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
      rw [Finset.sum_Ico_succ_top hm, ← ih]
      have h2m : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      exact (intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_one_div_log (a := (2:ℝ)) (b := (m:ℝ)) (by norm_num) h2m)
        (intervalIntegrable_one_div_log (a := (m:ℝ)) (b := (m:ℝ)+1) h2m (by linarith))).symm

/-- LEAF: The sum of the endpoint differences telescopes. -/
lemma sum_diff_Ico (N : ℕ) (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Ico 2 N, (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1)))
      = 1 / Real.log 2 - 1 / Real.log (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
      rw [Finset.sum_Ico_succ_top hm, ih]
      have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [hcast]; ring

/-- LEAF: Sum and integral of `1/log` over `[2, N]` differ by at most `1/log 2`. -/
lemma sum_sub_integral_abs_le (N : ℕ) (hN : 2 ≤ N) :
    |(∑ n ∈ Finset.Icc 2 N, 1 / Real.log (n : ℝ))
        - ∫ t in (2 : ℝ)..(N : ℝ), 1 / Real.log t| ≤ 1 / Real.log 2 := by
  have hf2pos : 0 < 1 / Real.log 2 := div_pos one_pos (Real.log_pos (by norm_num))
  have hIco : (∑ n ∈ Finset.Icc 2 N, 1 / Real.log (n : ℝ))
      = (∑ n ∈ Finset.Ico 2 N, 1 / Real.log (n : ℝ)) + 1 / Real.log (N : ℝ) := by
    rw [← Finset.Ico_insert_right hN, Finset.sum_insert (by simp), add_comm]
  set t : ℕ → ℝ := fun n => 1 / Real.log (n : ℝ) - ∫ x in (n : ℝ)..((n : ℝ) + 1), 1 / Real.log x with ht
  have hterm_low : ∀ n ∈ Finset.Ico 2 N, 0 ≤ t n := by
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Ico.mp hn).1
    have h := (unit_interval_bounds n hn2).2
    simp only [ht]
    linarith
  have hterm_up : ∀ n ∈ Finset.Ico 2 N, t n ≤ 1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1) := by
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Ico.mp hn).1
    have h := (unit_interval_bounds n hn2).1
    simp only [ht]
    linarith
  have hsum_low : 0 ≤ ∑ n ∈ Finset.Ico 2 N, t n := Finset.sum_nonneg hterm_low
  have hsum_up : (∑ n ∈ Finset.Ico 2 N, t n) ≤ 1 / Real.log 2 - 1 / Real.log (N : ℝ) := by
    calc (∑ n ∈ Finset.Ico 2 N, t n)
        ≤ ∑ n ∈ Finset.Ico 2 N, (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1)) :=
          Finset.sum_le_sum hterm_up
      _ = 1 / Real.log 2 - 1 / Real.log (N : ℝ) := sum_diff_Ico N hN
  have hsplit : (∑ n ∈ Finset.Ico 2 N, 1 / Real.log (n : ℝ))
      - ∫ t in (2 : ℝ)..(N : ℝ), 1 / Real.log t = ∑ n ∈ Finset.Ico 2 N, t n := by
    rw [integral_eq_sum_Ico N hN, ← Finset.sum_sub_distrib]
  have hfNpos : 0 ≤ 1 / Real.log (N : ℝ) :=
    le_of_lt (div_pos one_pos (Real.log_pos (by linarith [show (2:ℝ) ≤ N from by exact_mod_cast hN])))
  have hgoal : (∑ n ∈ Finset.Icc 2 N, 1 / Real.log (n : ℝ))
      - ∫ t in (2 : ℝ)..(N : ℝ), 1 / Real.log t
      = (∑ n ∈ Finset.Ico 2 N, t n) + 1 / Real.log (N : ℝ) := by
    rw [hIco]
    linarith
  rw [hgoal]
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith

/-- LEAF: `liD` agrees with the logarithmic integral up to `3`. -/
lemma abs_liD_sub_integral_le (x : ℝ) (hx : 2 ≤ x) :
    |LeanLab.PNTPort.BVMax.liD x - ∫ t in (2 : ℝ)..x, 1 / Real.log t| ≤ 3 := by
  have hN : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
  have hNR : (2 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hN
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxN : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hli : LeanLab.PNTPort.BVMax.liD x
      = ∑ n ∈ Finset.Icc 2 ⌊x⌋₊, 1 / Real.log (n : ℝ) := by
    have hsplit : Finset.Icc 1 ⌊x⌋₊ = insert 1 (Finset.Icc 2 ⌊x⌋₊) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have h1not : (1 : ℕ) ∉ Finset.Icc 2 ⌊x⌋₊ := by
      simp only [Finset.mem_Icc, not_and]
      omega
    simp only [LeanLab.PNTPort.BVMax.liD, LeanLab.PNTPort.BVMax.liN, hsplit,
      Finset.sum_insert h1not, Nat.cast_one, Real.log_one, div_zero, zero_add]
  have h1 : |(∑ n ∈ Finset.Icc 2 ⌊x⌋₊, 1 / Real.log (n : ℝ))
      - ∫ t in (2 : ℝ)..(⌊x⌋₊ : ℝ), 1 / Real.log t| ≤ 1 / Real.log 2 :=
    sum_sub_integral_abs_le ⌊x⌋₊ hN
  have htail : |∫ t in (⌊x⌋₊ : ℝ)..x, 1 / Real.log t| ≤ 1 / Real.log 2 := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (⌊x⌋₊ : ℝ)) (b := x) (C := 1 / Real.log (⌊x⌋₊ : ℝ))
      (f := fun t : ℝ => 1 / Real.log t) (fun t ht => by
        rw [Set.uIoc_of_le hNx] at ht
        have ht1 : (⌊x⌋₊ : ℝ) < t := ht.1
        have hlog : 0 < Real.log t := Real.log_pos (by linarith)
        have hle : 1 / Real.log t ≤ 1 / Real.log (⌊x⌋₊ : ℝ) :=
          one_div_le_one_div_of_le (Real.log_pos (by linarith))
            (Real.log_le_log (by linarith) (le_of_lt ht1))
        rw [Real.norm_eq_abs, abs_of_pos (div_pos one_pos hlog)]
        exact hle)
    have hb' : |∫ t in (⌊x⌋₊ : ℝ)..x, 1 / Real.log t|
        ≤ (1 / Real.log (⌊x⌋₊ : ℝ)) * (x - (⌊x⌋₊ : ℝ)) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - (⌊x⌋₊ : ℝ))] using hb
    have hC : 0 ≤ 1 / Real.log (⌊x⌋₊ : ℝ) :=
      le_of_lt (div_pos one_pos (Real.log_pos (by linarith)))
    have hfN : 1 / Real.log (⌊x⌋₊ : ℝ) ≤ 1 / Real.log 2 :=
      one_div_le_one_div_of_le (Real.log_pos (by norm_num))
        (Real.log_le_log (by norm_num) hNR)
    have hlen : x - (⌊x⌋₊ : ℝ) ≤ 1 := by linarith
    have hstep : (1 / Real.log (⌊x⌋₊ : ℝ)) * (x - (⌊x⌋₊ : ℝ)) ≤ 1 / Real.log 2 := by
      calc (1 / Real.log (⌊x⌋₊ : ℝ)) * (x - (⌊x⌋₊ : ℝ))
          ≤ (1 / Real.log (⌊x⌋₊ : ℝ)) * 1 := mul_le_mul_of_nonneg_left hlen hC
        _ = 1 / Real.log (⌊x⌋₊ : ℝ) := by ring
        _ ≤ 1 / Real.log 2 := hfN
    linarith
  have hsplit2 : (∫ t in (2 : ℝ)..x, 1 / Real.log t)
      = (∫ t in (2 : ℝ)..(⌊x⌋₊ : ℝ), 1 / Real.log t)
        + ∫ t in (⌊x⌋₊ : ℝ)..x, 1 / Real.log t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_one_div_log (by norm_num) hNR)
      (intervalIntegrable_one_div_log hNR hNx)).symm
  have hf2 : 1 / Real.log 2 ≤ 3 / 2 := by
    have hlog : (2 : ℝ) / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    rw [div_le_iff₀ (Real.log_pos (by norm_num))]
    linarith
  have htri : |(∑ n ∈ Finset.Icc 2 ⌊x⌋₊, 1 / Real.log (n : ℝ))
      - ((∫ t in (2 : ℝ)..(⌊x⌋₊ : ℝ), 1 / Real.log t)
        + ∫ t in (⌊x⌋₊ : ℝ)..x, 1 / Real.log t)| ≤ 1 / Real.log 2 + 1 / Real.log 2 := by
    have h := abs_sub ((∑ n ∈ Finset.Icc 2 ⌊x⌋₊, 1 / Real.log (n : ℝ))
        - ∫ t in (2 : ℝ)..(⌊x⌋₊ : ℝ), 1 / Real.log t)
        (∫ t in (⌊x⌋₊ : ℝ)..x, 1 / Real.log t)
    have heq : |(∑ n ∈ Finset.Icc 2 ⌊x⌋₊, 1 / Real.log (n : ℝ))
        - ((∫ t in (2 : ℝ)..(⌊x⌋₊ : ℝ), 1 / Real.log t)
          + ∫ t in (⌊x⌋₊ : ℝ)..x, 1 / Real.log t)|
        = |((∑ n ∈ Finset.Icc 2 ⌊x⌋₊, 1 / Real.log (n : ℝ))
          - ∫ t in (2 : ℝ)..(⌊x⌋₊ : ℝ), 1 / Real.log t)
          - ∫ t in (⌊x⌋₊ : ℝ)..x, 1 / Real.log t| := by ring_nf
    rw [heq]
    exact le_trans h (add_le_add h1 htail)
  rw [hli, hsplit2]
  linarith

/-- LEAF: Eventually every fixed power of `log` is below `sqrt`. -/
lemma eventually_log_rpow_le_sqrt (r : ℝ) :
    ∀ᶠ T : ℝ in Filter.atTop, Real.log T ^ r ≤ Real.sqrt T := by
  have h : (fun x : ℝ => Real.log x ^ r) =o[Filter.atTop] (fun x : ℝ => x ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop r (by norm_num)
  have ht : Filter.Tendsto (fun T : ℝ => Real.log T ^ r / T ^ (1 / 2 : ℝ))
      Filter.atTop (nhds 0) := h.tendsto_div_nhds_zero
  have hev : ∀ᶠ x : ℝ in nhds (0 : ℝ), x < 1 :=
    isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1)
  filter_upwards [ht.eventually hev, Filter.eventually_gt_atTop (0 : ℝ)] with T hlt hT0
  have hsT : 0 < T ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have h1 : Real.log T ^ r ≤ T ^ (1 / 2 : ℝ) := by
    have hh := mul_lt_mul_of_pos_right hlt hsT
    rw [div_mul_cancel₀ _ (ne_of_gt hsT), one_mul] at hh
    exact hh.le
  rw [Real.sqrt_eq_rpow]
  exact h1

/-- LEAF: Maximal Bombieri--Vinogradov for `primeError`, from the lab's unconditional `BVPi`. -/
theorem maximal_bv_pi (A : ℝ) (hA : 0 < A) :
    ∃ b C T0 : ℝ, 0 < b ∧ 0 < C ∧ 2 ≤ T0 ∧
      ∀ T : ℝ, T0 ≤ T → ∀ D : ℕ,
        (D : ℝ) ≤ Real.sqrt T * Real.log T ^ (-b) →
        (∑ d ∈ Finset.Icc 1 D, Task542a.primeError T d) ≤ C * T * Real.log T ^ (-A) := by
  obtain ⟨B, hB, K, hK⟩ := bvPi_unconditional (2 * A + 6) (by linarith)
  obtain ⟨T1, hT1⟩ := Filter.eventually_atTop.mp
    ((eventually_log_rpow_le_sqrt (max (A - B) 0)).and (Filter.eventually_ge_atTop (1 : ℝ)))
  refine ⟨B, max K 0 + 4, max (max 2 (Real.exp 1)) T1, hB, by positivity, ?_, ?_⟩
  · exact le_trans (le_max_left 2 (Real.exp 1)) (le_max_left _ _)
  intro T hT D hD
  have hT0 : max (max 2 (Real.exp 1)) T1 ≤ T := hT
  have hT2 : 2 ≤ T := le_trans (le_trans (le_max_left 2 (Real.exp 1)) (le_max_left _ _)) hT0
  have hTexp : Real.exp 1 ≤ T :=
    le_trans (le_trans (le_max_right 2 (Real.exp 1)) (le_max_left _ _)) hT0
  have hTge1 : (1 : ℝ) ≤ T := by linarith
  have hL1 : 1 ≤ Real.log T := by
    have h := Real.log_le_log (Real.exp_pos 1) hTexp
    simpa only [Real.log_exp] using h
  have hL : 0 < Real.log T := lt_of_lt_of_le zero_lt_one hL1
  have hsqrtT : Real.sqrt T ≤ T := by
    nlinarith [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ T), Real.sqrt_nonneg T]
  have hlogpow : Real.log T ^ (A - B) ≤ Real.sqrt T := by
    have h := hT1 T (le_trans (le_max_right (max 2 (Real.exp 1)) T1) hT0)
    rcases le_or_gt (A - B) 0 with hc | hc
    · have hle : Real.log T ^ (A - B) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 hc
      have h1 : 1 ≤ Real.sqrt T := Real.one_le_sqrt.mpr hTge1
      linarith
    · have h' := h.1
      rwa [max_eq_left hc.le] at h'
  have hlpowB : Real.log T ^ (-B) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  -- the modulus level is below `sqrt T`
  have hDT : (D : ℝ) ≤ T := by
    have h1 : (D : ℝ) ≤ Real.sqrt T * Real.log T ^ (-B) := hD
    have h2 : Real.sqrt T * Real.log T ^ (-B) ≤ Real.sqrt T := by
      calc Real.sqrt T * Real.log T ^ (-B) ≤ Real.sqrt T * 1 := by
            exact mul_le_mul_of_nonneg_left hlpowB (Real.sqrt_nonneg T)
        _ = Real.sqrt T := by ring
    linarith
  -- the approximation step
  set ε : ℝ := T * Real.log T ^ (-(2 * A + 6)) / (D + 1) with hεdef
  have hε : 0 < ε := by
    have h1 : 0 < T * Real.log T ^ (-(2 * A + 6)) :=
      mul_pos (by linarith) (Real.rpow_pos_of_pos hL _)
    have h2 : (0 : ℝ) < (D : ℝ) + 1 := by positivity
    rw [hεdef]
    exact div_pos h1 h2
  have hnear : ∀ d, d ∈ Finset.Icc 1 D →
      ∃ a : ℕ, ∃ x : ℝ, a < d ∧ Nat.Coprime a d ∧ 2 ≤ x ∧ x ≤ T ∧
        Task542a.primeError T d - ε ≤
          |Task542a.primeAP x d a
            - (∫ t in (2 : ℝ)..x, 1 / Real.log t) / (Nat.totient d : ℝ)| := by
    intro d hd
    obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
    have hdpos : 0 < d := hd1
    have hdTR : (d : ℝ) ≤ T := by
      have h1 : (d : ℝ) ≤ (D : ℝ) := by exact_mod_cast hdD
      linarith
    by_cases hlow : Task542a.primeError T d - ε ≤ 0
    · rcases Nat.lt_or_ge 1 d with h2 | h2
      · refine ⟨1, 2, h2, Nat.coprime_one_left d, by norm_num, hT2, ?_⟩
        have h0 : (0 : ℝ) ≤ |Task542a.primeAP 2 d 1
            - (∫ t in (2 : ℝ)..(2 : ℝ), 1 / Real.log t) / (Nat.totient d : ℝ)| := abs_nonneg _
        linarith
      · have hd1' : d = 1 := le_antisymm h2 hd1
        subst hd1'
        refine ⟨0, 2, by norm_num, by simp, by norm_num, hT2, ?_⟩
        have h0 : (0 : ℝ) ≤ |Task542a.primeAP 2 1 0
            - (∫ t in (2 : ℝ)..(2 : ℝ), 1 / Real.log t) / (Nat.totient 1 : ℝ)| := abs_nonneg _
        linarith
    · push_neg at hlow
      have hbdd := Task542a.primeError_bddAbove T d hT2 hL1 hdpos hdTR
      have hne : (insert 0 {v : ℝ | ∃ a : ℕ, ∃ x : ℝ, a < d ∧ Nat.Coprime a d ∧ 2 ≤ x ∧
          x ≤ T ∧ v = |Task542a.primeAP x d a
            - (∫ t in (2 : ℝ)..x, 1 / Real.log t) / Nat.totient d|}).Nonempty :=
        Set.insert_nonempty _ _
      have hlt : Task542a.primeError T d - ε <
          sSup (insert 0 {v : ℝ | ∃ a : ℕ, ∃ x : ℝ, a < d ∧ Nat.Coprime a d ∧ 2 ≤ x ∧
            x ≤ T ∧ v = |Task542a.primeAP x d a
              - (∫ t in (2 : ℝ)..x, 1 / Real.log t) / Nat.totient d|}) := by
        have h1 : Task542a.primeError T d - ε < Task542a.primeError T d := by linarith
        exact h1
      obtain ⟨v, hv, hzv⟩ := exists_lt_of_lt_csSup hne hlt
      rcases Set.mem_insert_iff.mp hv with h0 | hv'
      · rw [h0] at hzv
        linarith
      · obtain ⟨a, x, ha, hcop, hx2, hxT, hval⟩ := hv'
        exact ⟨a, x, ha, hcop, hx2, hxT, by rw [← hval]; exact hzv.le⟩
  -- choice functions
  let aa : ℕ → ℕ := fun d => if h : d ∈ Finset.Icc 1 D then (hnear d h).choose else 1
  let yy : ℕ → ℝ := fun d => if h : d ∈ Finset.Icc 1 D then (hnear d h).choose_spec.choose else 2
  have haa : ∀ d (h : d ∈ Finset.Icc 1 D), aa d = (hnear d h).choose := by
    intro d h
    simp only [aa, dif_pos h]
  have hyy' : ∀ d (h : d ∈ Finset.Icc 1 D), yy d = (hnear d h).choose_spec.choose := by
    intro d h
    simp only [yy, dif_pos h]
  have hcop : ∀ q, Nat.Coprime (aa q) q := by
    intro q
    by_cases hq : q ∈ Finset.Icc 1 D
    · rw [haa q hq]
      exact (hnear q hq).choose_spec.choose_spec.2.1
    · have h1 : aa q = 1 := by simp only [aa, dif_neg hq]
      rw [h1]
      exact Nat.coprime_one_left q
  have hspec : ∀ d (h : d ∈ Finset.Icc 1 D),
      (hnear d h).choose < d ∧ Nat.Coprime (hnear d h).choose d ∧
        2 ≤ (hnear d h).choose_spec.choose ∧ (hnear d h).choose_spec.choose ≤ T ∧
        Task542a.primeError T d - ε ≤ |Task542a.primeAP (hnear d h).choose_spec.choose d
          (hnear d h).choose
          - (∫ t in (2 : ℝ)..(hnear d h).choose_spec.choose, 1 / Real.log t)
            / (Nat.totient d : ℝ)| :=
    fun d h => (hnear d h).choose_spec.choose_spec
  have hyy : ∀ q, 0 ≤ yy q ∧ yy q ≤ T := by
    intro q
    by_cases hq : q ∈ Finset.Icc 1 D
    · rw [hyy' q hq]
      exact ⟨by linarith [(hspec q hq).2.2.1], (hspec q hq).2.2.2.1⟩
    · have h1 : yy q = 2 := by simp only [yy, dif_neg hq]
      rw [h1]
      exact ⟨by norm_num, hT2⟩
  -- the level condition and the Bombieri--Vinogradov sum
  have hQ : ∀ d ∈ Finset.Icc 1 D, d ≤ ⌊Real.sqrt T / Real.log T ^ B⌋₊ := by
    intro d hd
    have h1 : (d : ℝ) ≤ (D : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd).2
    have h2 : Real.sqrt T * Real.log T ^ (-B) = Real.sqrt T / Real.log T ^ B := by
      rw [Real.rpow_neg hL.le, div_eq_mul_inv]
    rw [h2] at hD
    exact Nat.le_floor (by linarith)
  have hbv : (∑ q ∈ Finset.Icc 1 ⌊Real.sqrt T / Real.log T ^ B⌋₊,
        |LeanLab.PNTPort.BVMax.piAP (yy q) q (aa q)
          - LeanLab.PNTPort.BVMax.liD (yy q) / (Nat.totient q : ℝ)|)
      ≤ K * T * Real.log T ^ (-(2 * A + 6)) := by
    have h0 := hK T hT2 aa hcop yy hyy
    have h1 : K * T / Real.log T ^ (2 * A + 6)
        = K * T * Real.log T ^ (-(2 * A + 6)) := by
      rw [Real.rpow_neg hL.le, div_eq_mul_inv]
    rwa [h1] at h0
  have hsub : (∑ d ∈ Finset.Icc 1 D,
        |LeanLab.PNTPort.BVMax.piAP (yy d) d (aa d)
          - LeanLab.PNTPort.BVMax.liD (yy d) / (Nat.totient d : ℝ)|)
      ≤ K * T * Real.log T ^ (-(2 * A + 6)) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hbv
    · intro d hd
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, hQ d hd⟩
    · intro d _ _
      exact abs_nonneg _
  -- pointwise comparison with the integral form
  have hpoint : ∀ d ∈ Finset.Icc 1 D,
      |Task542a.primeAP (yy d) d (aa d)
          - (∫ t in (2 : ℝ)..yy d, 1 / Real.log t) / (Nat.totient d : ℝ)|
        ≤ |LeanLab.PNTPort.BVMax.piAP (yy d) d (aa d)
            - LeanLab.PNTPort.BVMax.liD (yy d) / (Nat.totient d : ℝ)| + 3 := by
    intro d hd
    have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
    have hphi : 0 < (Nat.totient d : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hdpos
    have hy2 : 2 ≤ yy d := by
      rw [hyy' d hd]
      exact (hspec d hd).2.2.1
    have h3 := abs_liD_sub_integral_le (yy d) hy2
    have hpa : LeanLab.PNTPort.BVMax.piAP (yy d) d (aa d) = Task542a.primeAP (yy d) d (aa d) :=
      piAP_eq_primeAP (yy d) d (aa d)
    rw [hpa]
    have hkey : Task542a.primeAP (yy d) d (aa d)
          - (∫ t in (2 : ℝ)..yy d, 1 / Real.log t) / (Nat.totient d : ℝ)
        = (Task542a.primeAP (yy d) d (aa d)
            - LeanLab.PNTPort.BVMax.liD (yy d) / (Nat.totient d : ℝ))
          + (LeanLab.PNTPort.BVMax.liD (yy d)
            - ∫ t in (2 : ℝ)..yy d, 1 / Real.log t) / (Nat.totient d : ℝ) := by
      rw [div_eq_mul_inv]
      ring
    rw [hkey]
    have htri : |(Task542a.primeAP (yy d) d (aa d)
          - LeanLab.PNTPort.BVMax.liD (yy d) / (Nat.totient d : ℝ))
        + (LeanLab.PNTPort.BVMax.liD (yy d)
          - ∫ t in (2 : ℝ)..yy d, 1 / Real.log t) / (Nat.totient d : ℝ)|
        ≤ |Task542a.primeAP (yy d) d (aa d)
            - LeanLab.PNTPort.BVMax.liD (yy d) / (Nat.totient d : ℝ)|
          + |(LeanLab.PNTPort.BVMax.liD (yy d)
            - ∫ t in (2 : ℝ)..yy d, 1 / Real.log t) / (Nat.totient d : ℝ)| := by
      refine abs_le.mpr ⟨?_, ?_⟩
      · linarith [neg_abs_le (Task542a.primeAP (yy d) d (aa d)
            - LeanLab.PNTPort.BVMax.liD (yy d) / (Nat.totient d : ℝ)),
          neg_abs_le ((LeanLab.PNTPort.BVMax.liD (yy d)
            - ∫ t in (2 : ℝ)..yy d, 1 / Real.log t) / (Nat.totient d : ℝ))]
      · linarith [le_abs_self (Task542a.primeAP (yy d) d (aa d)
            - LeanLab.PNTPort.BVMax.liD (yy d) / (Nat.totient d : ℝ)),
          le_abs_self ((LeanLab.PNTPort.BVMax.liD (yy d)
            - ∫ t in (2 : ℝ)..yy d, 1 / Real.log t) / (Nat.totient d : ℝ))]
    refine le_trans htri ?_
    have h4 : |(LeanLab.PNTPort.BVMax.liD (yy d)
        - ∫ t in (2 : ℝ)..yy d, 1 / Real.log t) / (Nat.totient d : ℝ)| ≤ 3 := by
      rw [abs_div, abs_of_pos hphi]
      have h6 : 3 / (Nat.totient d : ℝ) ≤ 3 := by
        rw [div_le_iff₀ hphi]
        have h7 : (1 : ℝ) ≤ (Nat.totient d : ℝ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.totient_pos.mpr hdpos).ne'
        nlinarith
      calc |LeanLab.PNTPort.BVMax.liD (yy d)
          - ∫ t in (2 : ℝ)..yy d, 1 / Real.log t| / (Nat.totient d : ℝ)
          ≤ 3 / (Nat.totient d : ℝ) := by gcongr
        _ ≤ 3 := h6
    linarith
  -- sum of the comparison
  have hsum2 : (∑ d ∈ Finset.Icc 1 D, |Task542a.primeAP (yy d) d (aa d)
        - (∫ t in (2 : ℝ)..yy d, 1 / Real.log t) / (Nat.totient d : ℝ)|)
      ≤ K * T * Real.log T ^ (-(2 * A + 6)) + 3 * D := by
    have hsum3 : (∑ d ∈ Finset.Icc 1 D, |Task542a.primeAP (yy d) d (aa d)
          - (∫ t in (2 : ℝ)..yy d, 1 / Real.log t) / (Nat.totient d : ℝ)|)
        ≤ ∑ d ∈ Finset.Icc 1 D,
          (|LeanLab.PNTPort.BVMax.piAP (yy d) d (aa d)
              - LeanLab.PNTPort.BVMax.liD (yy d) / (Nat.totient d : ℝ)| + 3) :=
      Finset.sum_le_sum hpoint
    have hsum4 : (∑ d ∈ Finset.Icc 1 D,
          (|LeanLab.PNTPort.BVMax.piAP (yy d) d (aa d)
              - LeanLab.PNTPort.BVMax.liD (yy d) / (Nat.totient d : ℝ)| + 3))
        = (∑ d ∈ Finset.Icc 1 D,
            |LeanLab.PNTPort.BVMax.piAP (yy d) d (aa d)
              - LeanLab.PNTPort.BVMax.liD (yy d) / (Nat.totient d : ℝ)|)
          + 3 * (D : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel]
      push_cast
      ring
    rw [hsum4] at hsum3
    linarith
  -- assemble
  have hsumprime : (∑ d ∈ Finset.Icc 1 D, Task542a.primeError T d)
      ≤ (D : ℝ) * ε + (K * T * Real.log T ^ (-(2 * A + 6)) + 3 * D) := by
    have hd : (∑ d ∈ Finset.Icc 1 D, Task542a.primeError T d)
        ≤ ∑ d ∈ Finset.Icc 1 D, (ε + |Task542a.primeAP (yy d) d (aa d)
            - (∫ t in (2 : ℝ)..yy d, 1 / Real.log t) / (Nat.totient d : ℝ)|) := by
      refine Finset.sum_le_sum ?_
      intro d hd
      have := (hspec d hd).2.2.2.2
      rw [← hyy' d hd, ← haa d hd] at this
      linarith
    have hsplit : (∑ d ∈ Finset.Icc 1 D, (ε + |Task542a.primeAP (yy d) d (aa d)
          - (∫ t in (2 : ℝ)..yy d, 1 / Real.log t) / (Nat.totient d : ℝ)|))
        = (D : ℝ) * ε + ∑ d ∈ Finset.Icc 1 D, |Task542a.primeAP (yy d) d (aa d)
          - (∫ t in (2 : ℝ)..yy d, 1 / Real.log t) / (Nat.totient d : ℝ)| := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel]
      push_cast
      ring
    rw [hsplit] at hd
    linarith
  -- the three numerical absorptions
  have hDε : (D : ℝ) * ε ≤ T * Real.log T ^ (-(2 * A + 6)) := by
    have h1 : (0 : ℝ) ≤ T * Real.log T ^ (-(2 * A + 6)) :=
      le_of_lt (mul_pos (by linarith) (Real.rpow_pos_of_pos hL _))
    have h2 : (0 : ℝ) < (D : ℝ) + 1 := by positivity
    have h3 : (D : ℝ) / ((D : ℝ) + 1) ≤ 1 := by
      rw [div_le_one h2]
      linarith
    have h4 : (D : ℝ) * (T * Real.log T ^ (-(2 * A + 6)) / ((D : ℝ) + 1))
        = (T * Real.log T ^ (-(2 * A + 6))) * ((D : ℝ) / ((D : ℝ) + 1)) := by
      field_simp
    rw [hεdef, h4]
    calc (T * Real.log T ^ (-(2 * A + 6))) * ((D : ℝ) / ((D : ℝ) + 1))
        ≤ (T * Real.log T ^ (-(2 * A + 6))) * 1 := mul_le_mul_of_nonneg_left h3 h1
      _ = T * Real.log T ^ (-(2 * A + 6)) := by ring
  have h3D : 3 * (D : ℝ) ≤ 3 * T * Real.log T ^ (-A) := by
    have hD2 : (D : ℝ) ≤ Real.sqrt T * Real.log T ^ (-B) := hD
    have hsqrt : Real.sqrt T * Real.log T ^ (-B) ≤ T * Real.log T ^ (-A) := by
      have hpos : 0 < Real.log T ^ (-B) := Real.rpow_pos_of_pos hL _
      have hl : Real.log T ^ (-B) = Real.log T ^ (A - B) * Real.log T ^ (-A) := by
        rw [← Real.rpow_add hL]
        congr 1
        ring
      have h2 : Real.sqrt T * Real.log T ^ (A - B) ≤ T := by
        have h3 : Real.sqrt T * Real.log T ^ (A - B) ≤ Real.sqrt T * Real.sqrt T :=
          mul_le_mul_of_nonneg_left hlogpow (Real.sqrt_nonneg T)
        have h4 : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt (by linarith)
        calc Real.sqrt T * Real.log T ^ (A - B) ≤ Real.sqrt T * Real.sqrt T := h3
          _ = T := h4
      calc Real.sqrt T * Real.log T ^ (-B)
          = Real.sqrt T * (Real.log T ^ (A - B) * Real.log T ^ (-A)) := by rw [hl]
        _ = (Real.sqrt T * Real.log T ^ (A - B)) * Real.log T ^ (-A) := by rw [mul_assoc]
        _ ≤ T * Real.log T ^ (-A) :=
          mul_le_mul_of_nonneg_right h2 (le_of_lt (Real.rpow_pos_of_pos hL _))
    linarith
  have hKm : K * T * Real.log T ^ (-(2 * A + 6)) ≤ max K 0 * T * Real.log T ^ (-(2 * A + 6)) := by
    have h1 : K ≤ max K 0 := le_max_left _ _
    have h2 : (0 : ℝ) ≤ T * Real.log T ^ (-(2 * A + 6)) :=
      le_of_lt (mul_pos (by linarith) (Real.rpow_pos_of_pos hL _))
    have h3 := mul_le_mul_of_nonneg_right h1 h2
    calc K * T * Real.log T ^ (-(2 * A + 6))
        = K * (T * Real.log T ^ (-(2 * A + 6))) := by ring
      _ ≤ max K 0 * (T * Real.log T ^ (-(2 * A + 6))) := h3
      _ = max K 0 * T * Real.log T ^ (-(2 * A + 6)) := by ring
  have hfin : (max K 0 + 4) * T * Real.log T ^ (-A)
      = max K 0 * T * Real.log T ^ (-A) + 4 * (T * Real.log T ^ (-A)) := by ring
  have hlogA : Real.log T ^ (-(2 * A + 6)) ≤ Real.log T ^ (-A) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hTA : (0 : ℝ) ≤ T * Real.log T ^ (-A) :=
    le_of_lt (mul_pos (by linarith) (Real.rpow_pos_of_pos hL _))
  have h2A : T * Real.log T ^ (-(2 * A + 6)) ≤ T * Real.log T ^ (-A) :=
    mul_le_mul_of_nonneg_left hlogA (by linarith)
  have hstep2 : K * T * Real.log T ^ (-(2 * A + 6))
      ≤ max K 0 * T * Real.log T ^ (-A) := by
    have h1 : max K 0 * T * Real.log T ^ (-(2 * A + 6))
        ≤ max K 0 * T * Real.log T ^ (-A) := by
      have h0 : (0 : ℝ) ≤ max K 0 := le_max_right _ _
      calc max K 0 * T * Real.log T ^ (-(2 * A + 6))
          = max K 0 * (T * Real.log T ^ (-(2 * A + 6))) := by ring
        _ ≤ max K 0 * (T * Real.log T ^ (-A)) := mul_le_mul_of_nonneg_left h2A h0
        _ = max K 0 * T * Real.log T ^ (-A) := by ring
    linarith
  calc (∑ d ∈ Finset.Icc 1 D, Task542a.primeError T d)
      ≤ (D : ℝ) * ε + (K * T * Real.log T ^ (-(2 * A + 6)) + 3 * D) := hsumprime
    _ ≤ T * Real.log T ^ (-(2 * A + 6)) + (max K 0 * T * Real.log T ^ (-A)
          + 3 * T * Real.log T ^ (-A)) := by linarith
    _ ≤ max K 0 * T * Real.log T ^ (-A) + 4 * (T * Real.log T ^ (-A)) := by
        have : T * Real.log T ^ (-(2 * A + 6)) ≤ T * Real.log T ^ (-A) := h2A
        linarith
    _ = (max K 0 + 4) * T * Real.log T ^ (-A) := by ring


/-- LEAF: Divisor-weighted maximal Bombieri--Vinogradov. -/
theorem weighted_maximal_bv (A : ℝ) (hA : 0 < A) :
    ∃ b C T0 : ℝ, 0 < b ∧ 0 < C ∧ 2 ≤ T0 ∧
      ∀ T : ℝ, T0 ≤ T → ∀ D : ℕ,
        (D : ℝ) ≤ Real.sqrt T * Real.log T ^ (-b) →
        (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
          (d.divisors.card : ℝ) * Task542a.primeError T d) ≤ C * T * Real.log T ^ (-A) := by
  obtain ⟨b, C, T0, hb, hC, hT0, hBV⟩ := maximal_bv_pi (2 * A + 6) (by linarith)
  refine ⟨b, Real.sqrt (Real.exp 48 * (2 + 2 * Real.exp 24) * C),
    max T0 (Real.exp 1), hb, Real.sqrt_pos.mpr (by positivity),
    hT0.trans (le_max_left _ _), ?_⟩
  intro T hT D hD
  have hTbase : T0 ≤ T := (le_max_left _ _).trans hT
  have hT2 : 2 ≤ T := hT0.trans hTbase
  have hTe : Real.exp 1 ≤ T := (le_max_right _ _).trans hT
  have hL : 1 ≤ Real.log T := by
    have h := Real.log_le_log (Real.exp_pos 1) hTe
    simpa only [Real.log_exp] using h
  have hlpow : Real.log T ^ (-b) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  have hroot : Real.sqrt T ≤ T := by
    have hs := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ T)
    nlinarith [Real.sqrt_nonneg T]
  have hDT : (D : ℝ) ≤ T := hD.trans ((mul_le_of_le_one_right
    (Real.sqrt_nonneg T) hlpow).trans hroot)
  apply Task542a.weighted_prime_errors_of_sum D T A C hT2 hL hDT hC.le
  simpa only [neg_add_rev, neg_mul, neg_neg, add_comm, sub_eq_add_neg] using hBV T hTbase D hD

/-- LEAF: The divisor-weighted prime error sum over the prime window. -/
theorem prime_window_weighted_bv' (A B ε : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in Filter.atTop,
      (∑ p ∈ primeWindow X B ε,
        ∑ d ∈ (Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊).filter Squarefree,
          (d.divisors.card : ℝ) * Task542a.primeError (Real.sqrt (Y X ε) / p) d) ≤
        K * errorScale X ε A := by
  obtain ⟨b, C, T0, hb, hC, hT0, hBV⟩ := weighted_maximal_bv A hA
  let R : ℝ := 32 * (2 * B + 18)
  refine ⟨C * (8 : ℝ) ^ A * R, by dsimp [R]; positivity, ?_⟩
  filter_upwards [Task542a.prime_window_bv_parameters b T0 B ε hb hB hε hε1,
    prime_reciprocal_bound B ε hB hε,
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ)),
    Filter.eventually_gt_atTop (1 : ℝ)]
    with X hparams hrec hL1 hX
  have hL : 0 < Real.log X := hparams.1
  have hrecR : (∑ p ∈ primeWindow X B ε, (1 : ℝ) / p) ≤ R := by
    apply hrec.2.2.trans
    have hlog := Real.log_le_sub_one_of_pos hL
    apply (div_le_iff₀ hL).mpr
    dsimp [R]
    have hR : (0 : ℝ) ≤ 32 * (2 * B + 18) := by positivity
    nlinarith
  have hpow : (Real.log X / 8) ^ (-A) = (8 : ℝ) ^ A * Real.log X ^ (-A) := by
    rw [Real.div_rpow hL.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8),
      div_inv_eq_mul]
    ring
  have hlocal (p : ℕ) (hp : p ∈ primeWindow X B ε) :
      (∑ d ∈ (Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊).filter Squarefree,
        (d.divisors.card : ℝ) * Task542a.primeError (Real.sqrt (Y X ε) / p) d) ≤
      C * (Real.sqrt (Y X ε) / p) * ((8 : ℝ) ^ A * Real.log X ^ (-A)) := by
    obtain ⟨hT, hlog1, hloglo, hloghi, hlevel⟩ := hparams.2 p hp
    have hD : (⌊Y X ε ^ (1 / 9 : ℝ)⌋₊ : ℝ) ≤
        Real.sqrt (Real.sqrt (Y X ε) / p) * Real.log (Real.sqrt (Y X ε) / p) ^ (-b) :=
      (Nat.floor_le (Real.rpow_nonneg (by unfold Y; exact Real.rpow_nonneg (by linarith : 0 ≤ X) _) _)).trans hlevel
    apply (hBV _ hT _ hD).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← hpow]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hloglo (by linarith)
  calc (∑ p ∈ primeWindow X B ε,
        ∑ d ∈ (Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊).filter Squarefree,
          (d.divisors.card : ℝ) * Task542a.primeError (Real.sqrt (Y X ε) / p) d)
      ≤ ∑ p ∈ primeWindow X B ε,
        C * (Real.sqrt (Y X ε) / p) * ((8 : ℝ) ^ A * Real.log X ^ (-A)) :=
        Finset.sum_le_sum hlocal
    _ = (C * (8 : ℝ) ^ A * Real.sqrt (Y X ε) * Real.log X ^ (-A)) *
        ∑ p ∈ primeWindow X B ε, (1 : ℝ) / p := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ (C * (8 : ℝ) ^ A * Real.sqrt (Y X ε) * Real.log X ^ (-A)) * R :=
      mul_le_mul_of_nonneg_left hrecR (by positivity)
    _ = (C * (8 : ℝ) ^ A * R) * errorScale X ε A := by
      unfold errorScale
      rw [Real.sqrt_eq_rpow]
      ring

/-- LEAF: The full remainder estimate, from the unconditional maximal Bombieri--Vinogradov. -/
theorem bv_remainder_from_maximal' (A B ε : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) →
      (n : ℝ) ≤ X + Y X ε ^ (1 - ε) →
      remainder X B ε n ≤ C * errorScale X ε A := by
  obtain ⟨K, hK, hprime⟩ := prime_window_weighted_bv' A B ε hA hB hε hε1
  have hevent : ∀ᶠ X : ℝ in Filter.atTop,
      ∀ n : ℕ, X < (n : ℝ) → remainder X B ε n ≤ (2 * K + 4) * errorScale X ε A := by
    filter_upwards [hprime, Task542a.rough_level_parameters B ε hB hε hε1,
      Task542a.prime_window_bv_parameters 1 2 B ε (by norm_num) hB hε hε1,
      Task542a.endpoint_correction_bound A B ε hε] with X hp hr hw he
    intro n hXn
    have hparams : ∀ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
        ∀ p ∈ primeWindow X B ε, d < p ∧
          2 ≤ Real.sqrt (Y X ε) / p ∧ 1 ≤ Real.log (Real.sqrt (Y X ε) / p) ∧
            (d : ℝ) ≤ Real.sqrt (Y X ε) / p := by
      intro d hd p hpp
      obtain ⟨hT, hlog, hlo, hhi, hlevel⟩ := hw.2 p hpp
      have hdD : (d : ℝ) ≤ Y X ε ^ (1 / 9 : ℝ) :=
        (by exact_mod_cast (Finset.mem_Icc.mp hd).2 : (d : ℝ) ≤ ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊).trans
          (Nat.floor_le (Real.rpow_nonneg hr.1.le _))
      have hpz := (Finset.mem_filter.mp hpp).2.2.1
      have hdp : d < p := by exact_mod_cast (hdD.trans_lt (hr.2.2.trans_le hpz))
      have hlogpow : Real.log (Real.sqrt (Y X ε) / p) ^ (-(1 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hlog (by norm_num)
      have hroot : Real.sqrt (Real.sqrt (Y X ε) / p) ≤ Real.sqrt (Y X ε) / p := by
        have hh := Real.sq_sqrt (show 0 ≤ Real.sqrt (Y X ε) / p by positivity)
        nlinarith [Real.sqrt_nonneg (Real.sqrt (Y X ε) / p)]
      have hdT := hdD.trans (hlevel.trans ((mul_le_of_le_one_right
        (Real.sqrt_nonneg _) hlogpow).trans hroot))
      exact ⟨hdp, hT, hlog, hdT⟩
    have ht := Task542a.remainder_prime_transfer X B ε n hr.1 hr.2.1 hXn hparams
    nlinarith
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨2 * K + 4, X0, by positivity, ?_⟩
  intro X hX n hn hXn hnhi
  exact hX0 X hX n hXn

/-- LEAF: Step 1 of the split, the distribution input, now proved from the lab's
unconditional Siegel--Walfisz-based Bombieri--Vinogradov. -/
theorem weighted_modulus_discrepancy (A B ε : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) →
      (n : ℝ) ≤ X + Y X ε ^ (1 - ε) →
      ∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
          (ArithmeticFunction.moebius d : ℝ) ^ 2 *
            |progressionCount X B ε n d - density n d * primeMass X B ε| /
              (1 + Real.log (d : ℝ)) ≤ C * errorScale X ε (A + 1) := by
  obtain ⟨C, X0, hC, h⟩ := bv_remainder_from_maximal' (A + 1) B ε (by linarith) hB hε hε1
  refine ⟨C, X0, hC, ?_⟩
  intro X hX n hn hXn hnle
  refine (Finset.sum_le_sum ?_).trans (h X hX n hn hXn hnle)
  intro d hd
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hlog : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hd1R
  have hp : 0 < 1 + Real.log (d : ℝ) := by linarith
  have hle : 1 / (1 + Real.log (d : ℝ)) ≤ 1 := by
    rw [div_le_one hp]
    linarith
  have hnn : 0 ≤ (ArithmeticFunction.moebius d : ℝ) ^ 2 *
      |progressionCount X B ε n d - density n d * primeMass X B ε| :=
    mul_nonneg (sq_nonneg _) (abs_nonneg _)
  calc (ArithmeticFunction.moebius d : ℝ) ^ 2 *
        |progressionCount X B ε n d - density n d * primeMass X B ε| /
          (1 + Real.log (d : ℝ))
      = ((ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε|) *
            (1 / (1 + Real.log (d : ℝ))) := by ring
    _ ≤ ((ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε|) * 1 :=
        mul_le_mul_of_nonneg_left hle hnn
    _ = (ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε| := by ring



/-- LEAF: Step 2 of the split, the logarithmic size of the modulus range. With
`D = ⌊Y ^ (1 / 9)⌋` and `Y = X ^ (7 / 12 + ε / 2)`, every modulus `1 ≤ d ≤ D` has
`log d ≤ (8 / 81) log X`, so beyond a threshold `1 + log d ≤ 2 log X`. -/
theorem sieve_level_log_scale (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ X0 : ℝ, 0 < X0 ∧ ∀ X : ℝ, X0 ≤ X → ∀ d : ℕ, 1 ≤ d →
      d ≤ ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊ → 1 + Real.log (d : ℝ) ≤ 2 * Real.log X := by
  refine ⟨Real.exp 1, Real.exp_pos 1, ?_⟩
  intro X hX d hd1 hdD
  have hX1 : 1 ≤ X := (Real.one_le_exp zero_le_one).trans hX
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hL1 : 1 ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 1) hX
    rwa [Real.log_exp] at h
  have hL0 : 0 < Real.log X := lt_of_lt_of_le zero_lt_one hL1
  have hDpos : (0 : ℝ) < Y X ε ^ (1 / 9 : ℝ) :=
    Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hX0 _) _
  have hdle : (d : ℝ) ≤ X ^ (8 / 81 : ℝ) := by
    have h1 : (d : ℝ) ≤ (⌊Y X ε ^ (1 / 9 : ℝ)⌋₊ : ℝ) := by exact_mod_cast hdD
    have h2 : (⌊Y X ε ^ (1 / 9 : ℝ)⌋₊ : ℝ) ≤ Y X ε ^ (1 / 9 : ℝ) := Nat.floor_le hDpos.le
    have h3 : Y X ε ^ (1 / 9 : ℝ) ≤ X ^ (8 / 81 : ℝ) := by
      have hexp : (7 / 12 + ε / 2) * (1 / 9) ≤ 8 / 81 := by linarith
      calc Y X ε ^ (1 / 9 : ℝ) = (X ^ (7 / 12 + ε / 2)) ^ (1 / 9 : ℝ) := rfl
        _ = X ^ ((7 / 12 + ε / 2) * (1 / 9)) := (Real.rpow_mul hX0.le _ _).symm
        _ ≤ X ^ (8 / 81 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 hexp
    linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hlogd : Real.log (d : ℝ) ≤ 8 / 81 * Real.log X := by
    have h := Real.log_le_log hdpos hdle
    rwa [Real.log_rpow hX0] at h
  nlinarith

/-- LEAF: Step 3 of the split, the large-`X` regime of the parameters. Beyond a threshold
`log X ≥ 1`, the ninth power of the window `Y` is at least one, and the error scale at the
parameter `A` is nonnegative. These are the side conditions the assembly uses at every `X`
in the range. -/
theorem sieve_regime (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∃ X0 : ℝ, 0 < X0 ∧ ∀ X : ℝ, X0 ≤ X →
      1 ≤ Real.log X ∧ 1 ≤ Y X ε ^ (1 / 9 : ℝ) ∧ 0 ≤ errorScale X ε A := by
  refine ⟨Real.exp 1, Real.exp_pos 1, ?_⟩
  intro X hX
  have hX1 : 1 ≤ X := (Real.one_le_exp zero_le_one).trans hX
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hlog1 : 1 ≤ Real.log X := by
    have h := Real.log_le_log (Real.exp_pos 1) hX
    rwa [Real.log_exp] at h
  have hY1 : 1 ≤ Y X ε := by
    unfold Y
    exact Real.one_le_rpow hX1 (by linarith)
  have hY0 : 0 < Y X ε ^ (1 / 9 : ℝ) :=
    Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hX0 _) _
  refine ⟨hlog1, Real.one_le_rpow hY1 (by norm_num), ?_⟩
  unfold errorScale
  have h1 : 0 ≤ Y X ε ^ (1 / 2 : ℝ) := Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one hY1)) _
  have h2 : 0 ≤ Real.log X ^ (-A) :=
    le_of_lt (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hlog1) _)
  exact mul_nonneg h1 h2

/-- LEAF: Split of `bv_remainder`: the explicit squarefree remainder at level `Y ^ (1 / 9)` is at
most a constant times `Y ^ (1 / 2) * (log X) ^ (-A)`, from the three leaves above and the
definition of `remainder`. -/
theorem bv_remainder_split (A B ε : ℝ) (hA : 0 < A) (hB : 0 < B) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ C X0 : ℝ, 0 < C ∧ ∀ X : ℝ, X0 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) →
      (n : ℝ) ≤ X + Y X ε ^ (1 - ε) →
      remainder X B ε n ≤ C * errorScale X ε A := by
  obtain ⟨Cw, Xw, hCw, hw⟩ := weighted_modulus_discrepancy A B ε hA hB hε hε1
  obtain ⟨Xl, hXl, hl⟩ := sieve_level_log_scale ε hε hε1
  obtain ⟨Xr, hXr, hr⟩ := sieve_regime A ε hA hε
  refine ⟨2 * Cw, max Xw (max Xl Xr), by linarith, ?_⟩
  intro X hX n hn hXn hnle
  have hXw : Xw ≤ X := (le_max_left _ _).trans hX
  have hrest : max Xl Xr ≤ X := (le_max_right _ _).trans hX
  have hXl' : Xl ≤ X := (le_max_left _ _).trans hrest
  obtain ⟨hlog1, hY1, hE0⟩ := hr X ((le_max_right _ _).trans hrest)
  have hL : 0 < Real.log X := lt_of_lt_of_le zero_lt_one hlog1
  have hw' := hw X hXw n hn hXn hnle
  unfold remainder
  have hstep : ∀ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
      (ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε| ≤
        (2 * Real.log X) * ((ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε| /
            (1 + Real.log (d : ℝ))) := by
    intro d hd
    obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
    have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
    have hwpos : 0 < 1 + Real.log (d : ℝ) := by
      have hnn := Real.log_nonneg hd1R
      linarith
    have hwle : 1 + Real.log (d : ℝ) ≤ 2 * Real.log X := hl X hXl' d hd1 hdD
    have hu : 0 ≤ (ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε| /
            (1 + Real.log (d : ℝ)) :=
      div_nonneg (mul_nonneg (sq_nonneg _) (abs_nonneg _)) hwpos.le
    calc (ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε|
        = ((ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε| /
            (1 + Real.log (d : ℝ))) * (1 + Real.log (d : ℝ)) :=
          (div_mul_cancel₀ _ hwpos.ne').symm
      _ ≤ ((ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε| /
            (1 + Real.log (d : ℝ))) * (2 * Real.log X) :=
          mul_le_mul_of_nonneg_left hwle hu
      _ = (2 * Real.log X) * ((ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε| /
            (1 + Real.log (d : ℝ))) := by rw [mul_comm]
  calc ∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
        (ArithmeticFunction.moebius d : ℝ) ^ 2 *
          |progressionCount X B ε n d - density n d * primeMass X B ε|
      ≤ ∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
          (2 * Real.log X) * ((ArithmeticFunction.moebius d : ℝ) ^ 2 *
            |progressionCount X B ε n d - density n d * primeMass X B ε| /
              (1 + Real.log (d : ℝ))) := Finset.sum_le_sum hstep
    _ = (2 * Real.log X) * ∑ d ∈ Finset.Icc 1 ⌊Y X ε ^ (1 / 9 : ℝ)⌋₊,
          (ArithmeticFunction.moebius d : ℝ) ^ 2 *
            |progressionCount X B ε n d - density n d * primeMass X B ε| /
              (1 + Real.log (d : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ (2 * Real.log X) * (Cw * errorScale X ε (A + 1)) :=
        mul_le_mul_of_nonneg_left hw' (by linarith)
    _ = 2 * Cw * errorScale X ε A := by
        unfold errorScale
        have hkey : Real.log X * Real.log X ^ (-(A + 1)) = Real.log X ^ (-A) := by
          rw [show (-A : ℝ) = 1 + -(A + 1) by ring, Real.rpow_add hL, Real.rpow_one]
        calc (2 * Real.log X) * (Cw * (Y X ε ^ (1 / 2 : ℝ) * Real.log X ^ (-(A + 1))))
            = 2 * Cw * (Real.log X * Real.log X ^ (-(A + 1))) * Y X ε ^ (1 / 2 : ℝ) := by
              ring
          _ = 2 * Cw * (Y X ε ^ (1 / 2 : ℝ) * Real.log X ^ (-A)) := by
              rw [hkey]; ring

end LeanLab.KumchevLiu2007.Task506b
