import LeanLab.ChenDoubleSieve.Decomp363f
import LeanLab.ChenDoubleSieve.Decomp348m
import LeanLab.ChenDoubleSieve.Decomp363a
import LeanLab.ChenPrimeExceptional.Task101MertensLimit
import LeanLab.AlmostPrimeSums.Decomp1527c

/-!
Supply split for the ordinary upper bounds in Wu 2004.
Source: https://arxiv.org/pdf/0705.1652, page 39 equations 10.3 and 10.4.
The finite main terms retain the logarithmic sieve level loss.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- The upper endpoint for the prime band of each ordinary coordinate. -/
def basicEndpoint (i : Fin 12) : ℝ :=
  if i = 1 then kappa2 else if i = 2 then sigma1 else sigma2

/-- The sifting level is p in coordinate one and N to kappa one otherwise. -/
def basicSifting (N p : ℕ) (i : Fin 12) : ℝ :=
  if i = 1 then p else (N : ℝ) ^ kappa1

/-- The finite main term before replacing the prime sum by an integral.
The residual Q divided by p retains Q equal square root N over log N to B. -/
def basicMain (F : ℝ → ℝ) (B : ℝ) (N : ℕ) (i : Fin 12) : ℝ :=
  (N : ℝ) / log N * ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1)
      ((N : ℝ) ^ basicEndpoint i),
    Task363.localDensity N (basicSifting N p i) / ((p : ℝ) - 1) *
      F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / p) /
        log (basicSifting N p i))

/-! ### Floored power-cutoff logarithms

Copies of `Task101.log_floor_rpow_limit` / `log_floor_rpow_ratio`; the module
`Task101PowerCutoffs` is *not* in this file's closure, so the proofs are repeated
here (they use only `Task101MertensLimit`, which is). -/

theorem b349_floor_rpow_log_limit {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => log (⌊(n : ℝ) ^ a⌋₊ : ℝ) / log n) atTop (𝓝 a) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hr := tendsto_nat_floor_div_atTop.comp ht
  have hl := hr.log (by norm_num : (1 : ℝ) ≠ 0)
  have h0 := hl.div_atTop (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hs : Tendsto (fun n : ℕ => a +
      log ((⌊(n : ℝ) ^ a⌋₊ : ℝ) / ((n : ℝ) ^ a)) / log n) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.add h0
  apply hs.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ), ht.eventually_ge_atTop 2] with n hn hx
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hfloor : 0 < (⌊(n : ℝ) ^ a⌋₊ : ℝ) := by
    exact_mod_cast (Nat.floor_pos.mpr (show (1 : ℝ) ≤ (n : ℝ) ^ a by linarith))
  rw [log_div hfloor.ne' (rpow_pos_of_pos (by linarith : (0 : ℝ) < n) a).ne',
    log_rpow (by linarith : (0 : ℝ) < n)]
  field_simp [(log_pos hn').ne']
  ring

theorem b349_floor_rpow_log_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n : ℕ => log (⌊(n : ℝ) ^ a⌋₊ : ℝ) /
      log (⌊(n : ℝ) ^ b⌋₊ : ℝ)) atTop (𝓝 (a / b)) := by
  have h := (b349_floor_rpow_log_limit ha).div (b349_floor_rpow_log_limit hb) hb.ne'
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  exact div_div_div_cancel_right₀ (log_pos hn').ne' _ _

/-- The prime reciprocal mass of the floored band tends to the logarithmic ratio. -/
theorem b349_floor_band_mass_tendsto {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun N : ℕ => ∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ)) atTop (𝓝 (log (b / a))) := by
  have hb : 0 < b := ha.trans_le hab
  have hy : Tendsto (fun N : ℕ => ⌊(N : ℝ) ^ a⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop)
  have hlogy : Tendsto (fun N : ℕ => log (⌊(N : ℝ) ^ a⌋₊ : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hy)
  have herrbound : Tendsto (fun N : ℕ => 22 / log (⌊(N : ℝ) ^ a⌋₊ : ℝ)) atTop (𝓝 0) :=
    hlogy.const_div_atTop 22
  have hlogratio : Tendsto (fun N : ℕ =>
      log (log (⌊(N : ℝ) ^ b⌋₊ : ℝ) / log (⌊(N : ℝ) ^ a⌋₊ : ℝ)))
      atTop (𝓝 (log (b / a))) :=
    (b349_floor_rpow_log_ratio hb ha).log (div_pos hb ha).ne'
  have herr : Tendsto (fun N : ℕ =>
      (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) -
        log (log (⌊(N : ℝ) ^ b⌋₊ : ℝ) / log (⌊(N : ℝ) ^ a⌋₊ : ℝ))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) _ herrbound
    filter_upwards [hy.eventually_ge_atTop 2, eventually_ge_atTop (1 : ℕ)] with N hyN hN
    have horder : ⌊(N : ℝ) ^ a⌋₊ ≤ ⌊(N : ℝ) ^ b⌋₊ :=
      Nat.floor_mono (rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hab)
    have he := LeanLab.ChenPrimeExceptional.Task101.reciprocal_block_error hyN horder
    have hya : 0 < log (⌊(N : ℝ) ^ a⌋₊ : ℝ) :=
      log_pos (by exact_mod_cast (show 1 < ⌊(N : ℝ) ^ a⌋₊ by omega))
    have hwb : 0 < log (⌊(N : ℝ) ^ b⌋₊ : ℝ) :=
      log_pos (by exact_mod_cast (show 1 < ⌊(N : ℝ) ^ b⌋₊ by omega))
    rw [log_div hwb.ne' hya.ne', LeanLab.ChenPrimeExceptional.Task101.reciprocal_block_eq horder]
    exact he
  have ht := herr.add hlogratio
  simpa using ht

/-- The inverse of a floored power cutoff vanishes. -/
theorem b349_floor_inv_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => ((⌊(N : ℝ) ^ a⌋₊ : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
  have hy : Tendsto (fun N : ℕ => ⌊(N : ℝ) ^ a⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop)
  exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hy)

/-! ### Behaviour of `Wu41.PS` against the floored band -/

/-- `PS N (N^a) (N^b)` is contained in the floored band together with the single
left endpoint `⌊N^a⌋`. -/
theorem b349_PS_subset_insert (a b : ℝ) (N : ℕ) :
    Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b) ⊆
      insert ⌊(N : ℝ) ^ a⌋₊ ((Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime) := by
  intro p hp
  obtain ⟨hpp, hpa, hpb, hc⟩ := Wu41.mem_PS.mp hp
  have hpb' : p ≤ ⌊(N : ℝ) ^ b⌋₊ := by
    have h1 : (p : ℝ) < ((⌊(N : ℝ) ^ b⌋₊ : ℕ) : ℝ) + 1 :=
      lt_of_lt_of_le hpb (Nat.lt_floor_add_one ((N : ℝ) ^ b)).le
    have h2 : (p : ℝ) < (((⌊(N : ℝ) ^ b⌋₊ + 1 : ℕ)) : ℝ) := by push_cast; linarith
    have h3 : p < ⌊(N : ℝ) ^ b⌋₊ + 1 := by exact_mod_cast h2
    omega
  by_cases hq : ⌊(N : ℝ) ^ a⌋₊ < p
  · exact Finset.mem_insert_of_mem
      (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hq, hpb'⟩, hpp⟩)
  · push_neg at hq
    have hEq : p = ⌊(N : ℝ) ^ a⌋₊ := by
      have h1 : ((⌊(N : ℝ) ^ a⌋₊ : ℕ) : ℝ) ≤ (p : ℝ) :=
        le_trans (Nat.floor_le (by positivity)) hpa
      have h3 : (p : ℝ) ≤ ((⌊(N : ℝ) ^ a⌋₊ : ℕ) : ℝ) := by exact_mod_cast hq
      exact_mod_cast le_antisymm h3 h1
    exact Finset.mem_insert.mpr (Or.inl hEq)

/-- Every prime of the floored band is either in `PS`, or is the right endpoint
`⌊N^b⌋`, or divides `N`. -/
theorem b349_block_subset_insert (a b : ℝ) {N : ℕ} :
    (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime ⊆
      insert ⌊(N : ℝ) ^ b⌋₊ (Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b) ∪
        (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter
          (fun p => Nat.Prime p ∧ p ∣ N)) := by
  intro p hp
  obtain ⟨hIoc, hpp⟩ := Finset.mem_filter.mp hp
  obtain ⟨hq, hpbw⟩ := Finset.mem_Ioc.mp hIoc
  have hpa : (N : ℝ) ^ a ≤ (p : ℝ) := by
    have h1 : ((⌊(N : ℝ) ^ a⌋₊ + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (show ⌊(N : ℝ) ^ a⌋₊ + 1 ≤ p by omega)
    have h2 := Nat.lt_floor_add_one ((N : ℝ) ^ a)
    push_cast at h1
    linarith
  have hpw : (p : ℝ) ≤ ((⌊(N : ℝ) ^ b⌋₊ : ℕ) : ℝ) := by exact_mod_cast hpbw
  by_cases hsplit : (p : ℝ) < (N : ℝ) ^ b
  · by_cases hcop : p.Coprime N
    · exact Finset.mem_insert_of_mem
        (Finset.mem_union.mpr (Or.inl (Wu41.mem_PS.mpr ⟨hpp, hpa, hsplit, hcop⟩)))
    · have hpdvd : p ∣ N := by
        by_contra h
        exact hcop ((Nat.Prime.coprime_iff_not_dvd hpp).mpr h)
      exact Finset.mem_insert_of_mem
        (Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hIoc, hpp, hpdvd⟩)))
  · push_neg at hsplit
    have hwN : ((⌊(N : ℝ) ^ b⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) ^ b := Nat.floor_le (by positivity)
    have hEq : p = ⌊(N : ℝ) ^ b⌋₊ := by
      have hre : (p : ℝ) = ((⌊(N : ℝ) ^ b⌋₊ : ℕ) : ℝ) :=
        le_antisymm hpw (le_trans hwN hsplit)
      exact_mod_cast hre
    exact Finset.mem_insert.mpr (Or.inl hEq)

/-- `PS` and the non-coprime part of the floored band are disjoint. -/
theorem b349_PS_disjoint (a b : ℝ) (N : ℕ) :
    Disjoint (Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b))
      ((Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter
        (fun p => Nat.Prime p ∧ p ∣ N)) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  obtain ⟨hpp, -, -, hc⟩ := Wu41.mem_PS.mp hp
  have hdvd : p ∣ N := (Finset.mem_filter.mp hq).2.2
  exact hpp.one_lt.ne' (hc.eq_one_of_dvd hdvd)

/-- A product of distinct primes each dividing `N` divides `N`. -/
theorem b349_prod_dvd {N : ℕ} {S : Finset ℕ} (h : ∀ p ∈ S, p.Prime ∧ p ∣ N) :
    (S.prod id) ∣ N := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
      rw [Finset.prod_insert hp]
      have hps : p.Prime ∧ p ∣ N := h p (Finset.mem_insert_self p s)
      have hs : ∀ q ∈ s, q.Prime ∧ q ∣ N := fun q hq => h q (Finset.mem_insert_of_mem hq)
      have hcop : Nat.Coprime p (s.prod id) := by
        rw [Nat.coprime_prod_right_iff]
        intro q hq
        exact (Nat.coprime_primes hps.1 (hs q hq).1).mpr (fun hpq => hp (hpq ▸ hq))
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hps.2 (ih hs)

/-- The non-coprime part of a prime band above `N^a` has mass at most `1/(a N^a)`:
there are at most `1/a` such primes. -/
theorem b349_violator_mass_le {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : 2 ≤ N)
    {y : ℕ} (hy : (N : ℝ) ^ a ≤ (y : ℝ) + 1) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ∣ N ∧ y < p) :
    ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ≤ (1 / a) * (N : ℝ) ^ (-a) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hNgt : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hNapos : (0 : ℝ) < (N : ℝ) ^ a := Real.rpow_pos_of_pos hNpos a
  have hterm : ∀ p ∈ S, (1 : ℝ) / (p : ℝ) ≤ (N : ℝ) ^ (-a) := by
    intro p hp
    have hpge : (N : ℝ) ^ a ≤ (p : ℝ) := by
      have h1 : ((y + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (show y + 1 ≤ p by have := (hS p hp).2.2; omega)
      push_cast at h1
      linarith
    have hppos : (0 : ℝ) < (p : ℝ) := by
      have := (hS p hp).1.two_le
      exact_mod_cast (show 0 < p by omega)
    calc (1 : ℝ) / (p : ℝ) = ((p : ℝ))⁻¹ := one_div _
      _ ≤ ((N : ℝ) ^ a)⁻¹ := (inv_le_inv₀ hppos hNapos).mpr hpge
      _ = (N : ℝ) ^ (-a) := by rw [Real.rpow_neg hNpos.le]
  have hcard : ((S.card : ℕ) : ℝ) ≤ 1 / a := by
    rw [le_div_iff₀ ha]
    have hpdvd : (S.prod id) ∣ N :=
      b349_prod_dvd (fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩)
    have hprodle : S.prod id ≤ N := Nat.le_of_dvd (by omega) hpdvd
    have hprodge1 : (N : ℝ) ^ a ≤ ((y + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have hprodge : (y + 1) ^ S.card ≤ S.prod id := by
      have hstep : (∏ _p ∈ S, (y + 1)) ≤ ∏ p ∈ S, id p :=
        Finset.prod_le_prod (fun p hp => by have := (hS p hp).2.2; show y + 1 ≤ p; omega)
      rw [Finset.prod_const] at hstep
      simpa using hstep
    have hle : ((y + 1 : ℕ) : ℝ) ^ S.card ≤ (N : ℝ) := by
      have h1 : (y + 1) ^ S.card ≤ N := le_trans hprodge hprodle
      exact_mod_cast h1
    have hlogpos : 0 < log (N : ℝ) := log_pos hNgt
    have hlog1 : (S.card : ℝ) * log ((y + 1 : ℕ) : ℝ) ≤ log (N : ℝ) := by
      have hpos : (0 : ℝ) < ((y + 1 : ℕ) : ℝ) ^ S.card := by positivity
      have h := Real.log_le_log hpos hle
      rwa [Real.log_pow] at h
    have hlog2 : a * log (N : ℝ) ≤ log ((y + 1 : ℕ) : ℝ) := by
      have h := Real.log_le_log (Real.rpow_pos_of_pos hNpos a) hprodge1
      rwa [Real.log_rpow hNpos] at h
    have hcardnn : (0 : ℝ) ≤ ((S.card : ℕ) : ℝ) := by positivity
    have hstep2 : ((S.card : ℕ) : ℝ) * (a * log (N : ℝ)) ≤
        ((S.card : ℕ) : ℝ) * log ((y + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hlog2 hcardnn
    nlinarith [hstep2, hlog1, hlogpos]
  calc ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ≤ ∑ _p ∈ S, (N : ℝ) ^ (-a) := Finset.sum_le_sum hterm
    _ = ((S.card : ℕ) : ℝ) * (N : ℝ) ^ (-a) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (1 / a) * (N : ℝ) ^ (-a) :=
      mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hNpos.le _)

/-! ### The band mass for `Wu41.PS` -/

/-- Upper comparison of `PS` with the floored band. -/
theorem b349_PS_le_block (a b : ℝ) (N : ℕ) :
    (∑ p ∈ Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b), (1 : ℝ) / (p : ℝ)) ≤
      (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
        + ((⌊(N : ℝ) ^ a⌋₊ : ℕ) : ℝ)⁻¹ := by
  have hnn : ∀ p : ℕ, 0 ≤ (1 : ℝ) / (p : ℝ) :=
    fun p => div_nonneg zero_le_one (by positivity)
  have hsub := b349_PS_subset_insert a b N
  have h1 : (∑ p ∈ Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b), (1 : ℝ) / (p : ℝ)) ≤
      ∑ p ∈ insert ⌊(N : ℝ) ^ a⌋₊
        ((Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime), (1 : ℝ) / (p : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hnn p)
  have h2 : (∑ p ∈ insert ⌊(N : ℝ) ^ a⌋₊
        ((Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime), (1 : ℝ) / (p : ℝ)) ≤
      (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
        + ((⌊(N : ℝ) ^ a⌋₊ : ℕ) : ℝ)⁻¹ := by
    by_cases hq : ⌊(N : ℝ) ^ a⌋₊ ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime
    · rw [Finset.insert_eq_of_mem hq]
      have hpos : (0 : ℝ) ≤ ((⌊(N : ℝ) ^ a⌋₊ : ℕ) : ℝ)⁻¹ := by positivity
      linarith
    · rw [Finset.sum_insert hq]
      simp only [one_div]
      linarith
  linarith

/-- Lower comparison of the floored band with `PS`. -/
theorem b349_block_le_PS (a b : ℝ) (N : ℕ) :
    (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤
      (∑ p ∈ Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b), (1 : ℝ) / (p : ℝ))
        + ((⌊(N : ℝ) ^ b⌋₊ : ℕ) : ℝ)⁻¹
        + ∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter
            (fun p => Nat.Prime p ∧ p ∣ N), (1 : ℝ) / (p : ℝ) := by
  have hnn : ∀ p : ℕ, 0 ≤ (1 : ℝ) / (p : ℝ) :=
    fun p => div_nonneg zero_le_one (by positivity)
  have hsub := b349_block_subset_insert a b (N := N)
  have h1 : (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime,
        (1 : ℝ) / (p : ℝ)) ≤
      ∑ p ∈ insert ⌊(N : ℝ) ^ b⌋₊ (Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b) ∪
        (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter (fun p => Nat.Prime p ∧ p ∣ N)),
        (1 : ℝ) / (p : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hnn p)
  have h2 : (∑ p ∈ insert ⌊(N : ℝ) ^ b⌋₊ (Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b) ∪
        (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter (fun p => Nat.Prime p ∧ p ∣ N)),
        (1 : ℝ) / (p : ℝ)) ≤
      (∑ p ∈ Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b) ∪
        (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter (fun p => Nat.Prime p ∧ p ∣ N),
        (1 : ℝ) / (p : ℝ)) + ((⌊(N : ℝ) ^ b⌋₊ : ℕ) : ℝ)⁻¹ := by
    by_cases hq : ⌊(N : ℝ) ^ b⌋₊ ∈ Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b) ∪
        (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter (fun p => Nat.Prime p ∧ p ∣ N)
    · rw [Finset.insert_eq_of_mem hq]
      have hpos : (0 : ℝ) ≤ ((⌊(N : ℝ) ^ b⌋₊ : ℕ) : ℝ)⁻¹ := by positivity
      linarith
    · rw [Finset.sum_insert hq]
      simp only [one_div]
      linarith
  have h3 : (∑ p ∈ Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b) ∪
        (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter (fun p => Nat.Prime p ∧ p ∣ N),
        (1 : ℝ) / (p : ℝ)) =
      (∑ p ∈ Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b), (1 : ℝ) / (p : ℝ))
        + ∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter
            (fun p => Nat.Prime p ∧ p ∣ N), (1 : ℝ) / (p : ℝ) :=
    Finset.sum_union (b349_PS_disjoint a b N)
  linarith


/-! ### Vanishing negative powers and the non-coprime band -/

theorem b349_nat_rpow_neg {s : ℝ} (hs : 0 < s) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (-s)) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => (x ^ s)⁻¹) atTop (𝓝 0) :=
    (tendsto_rpow_atTop hs).inv_tendsto_atTop
  refine (h.comp tendsto_natCast_atTop_atTop).congr' ?_
  filter_upwards with N
  exact (Real.rpow_neg (Nat.cast_nonneg N) s).symm

/-- Primes of the floored band that divide `N` carry vanishing mass. -/
theorem b349_violators_tendsto {a b : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => ∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter
        (fun p => Nat.Prime p ∧ p ∣ N), (1 : ℝ) / (p : ℝ)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hbound : Tendsto (fun N : ℕ => ((N : ℝ) ^ (-a)) * (1 / a)) atTop (𝓝 0) := by
    simpa using (b349_nat_rpow_neg ha).mul_const (1 / a)
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) _ hbound
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hle := b349_violator_mass_le (a := a) ha hN
    (y := ⌊(N : ℝ) ^ a⌋₊)
    (S := (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter (fun p => Nat.Prime p ∧ p ∣ N))
    (Nat.lt_floor_add_one ((N : ℝ) ^ a)).le
    (fun p hp => by
      obtain ⟨hIoc, hpp, hpdvd⟩ := Finset.mem_filter.mp hp
      exact ⟨hpp, hpdvd, (Finset.mem_Ioc.mp hIoc).1⟩)
  have hnn : 0 ≤ ∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter
      (fun p => Nat.Prime p ∧ p ∣ N), (1 : ℝ) / (p : ℝ) :=
    Finset.sum_nonneg (fun p _ => div_nonneg zero_le_one (by positivity))
  rw [abs_of_nonneg hnn]
  calc _ ≤ (1 / a) * (N : ℝ) ^ (-a) := hle
    _ = (N : ℝ) ^ (-a) * (1 / a) := by ring

/-! ### The band mass for `Wu41.PS` -/

/-- The reciprocal prime mass of `Wu41.PS N (N^a) (N^b)` tends to `log (b / a)`. -/
theorem b349_ps_mass_tendsto {a b : ℝ} (ha : 0 < a) (ha1 : a < 1) (hab : a ≤ b) :
    Tendsto (fun N : ℕ => ∑ p ∈ Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b),
        (1 : ℝ) / (p : ℝ)) atTop (𝓝 (log (b / a))) := by
  have hb : 0 < b := ha.trans_le hab
  have hblk := b349_floor_band_mass_tendsto ha hab
  have hqa := b349_floor_inv_tendsto (a := a) ha
  have hqb := b349_floor_inv_tendsto (a := b) hb
  have hv := b349_violators_tendsto (a := a) (b := b) ha
  have hd : Tendsto (fun N : ℕ =>
      (∑ p ∈ Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b), (1 : ℝ) / (p : ℝ)) -
        (∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime,
          (1 : ℝ) / (p : ℝ))) atTop (𝓝 0) := by
    have hbound : Tendsto (fun N : ℕ =>
        ((⌊(N : ℝ) ^ a⌋₊ : ℕ) : ℝ)⁻¹ + ((⌊(N : ℝ) ^ b⌋₊ : ℕ) : ℝ)⁻¹ +
          ∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter
            (fun p => Nat.Prime p ∧ p ∣ N), (1 : ℝ) / (p : ℝ)) atTop (𝓝 0) := by
      have h := (hqa.add hqb).add hv
      simpa using h
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ hbound
    filter_upwards with N
    simp only [Function.comp_apply]
    have hA := b349_PS_le_block a b N
    have hB := b349_block_le_PS a b N
    rw [abs_sub_le_iff]
    have hb1 : 0 ≤ ((⌊(N : ℝ) ^ b⌋₊ : ℕ) : ℝ)⁻¹ := by positivity
    have hb2 : 0 ≤ ((⌊(N : ℝ) ^ a⌋₊ : ℕ) : ℝ)⁻¹ := by positivity
    have hv0 : 0 ≤ ∑ p ∈ (Finset.Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter
        (fun p => Nat.Prime p ∧ p ∣ N), (1 : ℝ) / (p : ℝ) :=
      Finset.sum_nonneg (fun p _ => div_nonneg zero_le_one (by positivity))
    constructor <;> linarith
  have h := hd.add hblk
  simpa only [sub_add_cancel, zero_add] using h

/-! ### The weighted band sum -/

/-- The band splits along any monotone partition of the exponent interval. -/
theorem b349_band_split {σ : ℝ} (N : ℕ) (hN : 1 ≤ N) {a : ℕ → ℝ} {m : ℕ} (hm1 : 1 ≤ m)
    (h0 : a 0 = kappa1) (hmm : a m = σ) (hmono : Monotone a) :
    Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ) =
      (Finset.range m).biUnion
        (fun j => Wu41.PS N ((N : ℝ) ^ a j) ((N : ℝ) ^ a (j + 1))) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  ext p
  rw [Finset.mem_biUnion]
  constructor
  · intro hp
    obtain ⟨hpp, hpa, hpb, hc⟩ := Wu41.mem_PS.mp hp
    have hwit : (p : ℝ) < (N : ℝ) ^ a (m - 1 + 1) := by
      rw [show m - 1 + 1 = m from by omega, hmm]
      exact hpb
    have hex : ∃ j, (p : ℝ) < (N : ℝ) ^ a (j + 1) := ⟨m - 1, hwit⟩
    have hle : Nat.find hex ≤ m - 1 := Nat.find_min' hex hwit
    refine ⟨Nat.find hex, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · have hspec := Nat.find_spec hex
      have hge : (N : ℝ) ^ a (Nat.find hex) ≤ (p : ℝ) := by
        rcases Nat.eq_zero_or_pos (Nat.find hex) with hz | hpos
        · rw [hz, h0]; exact hpa
        · obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i + 1 := ⟨Nat.find hex - 1, by omega⟩
          have hmin : ¬ ((p : ℝ) < (N : ℝ) ^ a (i + 1)) := Nat.find_min hex (by omega)
          rw [hi]
          exact not_lt.mp hmin
      exact Wu41.mem_PS.mpr ⟨hpp, hge, hspec, hc⟩
  · rintro ⟨j, hj, hpj⟩
    have hjm : j < m := Finset.mem_range.mp hj
    obtain ⟨hpp, hpa, hpb, hc⟩ := Wu41.mem_PS.mp hpj
    refine Wu41.mem_PS.mpr ⟨hpp, ?_, ?_, hc⟩
    · calc (N : ℝ) ^ kappa1 = (N : ℝ) ^ a 0 := by rw [h0]
        _ ≤ (N : ℝ) ^ a j := rpow_le_rpow_of_exponent_le hN1 (hmono (Nat.zero_le j))
        _ ≤ (p : ℝ) := hpa
    · calc (p : ℝ) < (N : ℝ) ^ a (j + 1) := hpb
        _ ≤ (N : ℝ) ^ a m := rpow_le_rpow_of_exponent_le hN1 (hmono (by omega))
        _ = (N : ℝ) ^ σ := by rw [hmm]

/-- Continuous weights on the ordinary band have the expected logarithmic integral. -/
theorem b349_band_sum_tendsto {σ : ℝ} (hκσ : kappa1 < σ) (hσ1 : σ ≤ 1)
    (Ψ : ℝ → ℝ) (hΨ : ContinuousOn Ψ (Set.Icc kappa1 σ)) :
    Tendsto (fun N : ℕ => ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
        Ψ (log (p : ℝ) / log N) / (p : ℝ)) atTop
      (𝓝 (∫ t in kappa1..σ, Ψ t / t)) := by
  have hκ1 : 0 < kappa1 := by norm_num [kappa1]
  have hκ1lt : kappa1 < 1 := by norm_num [kappa1]
  have hκ1σ : kappa1 ≤ σ := hκσ.le
  have hLpos : 0 < log (σ / kappa1) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hκ1]
    linarith
  have hmasslim := b349_ps_mass_tendsto (a := kappa1) (b := σ) hκ1 hκ1lt hκ1σ
  have hmassb : ∀ᶠ N : ℕ in atTop,
      (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ), (1 : ℝ) / (p : ℝ)) ≤
        log (σ / kappa1) + 1 :=
    hmasslim.eventually (eventually_le_nhds (by linarith))
  rw [Metric.tendsto_nhds]
  intro ε hε
  classical
  set e : ℝ := ε / (4 * (log (σ / kappa1) + 2)) with he
  have hepos : 0 < e := by
    rw [he]
    exact div_pos hε (by linarith)
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff_le.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hΨ) e hepos
  obtain ⟨m, hmδ⟩ := exists_nat_gt ((σ - kappa1) / δ)
  have hσδ : 0 < (σ - kappa1) / δ := div_pos (by linarith) hδpos
  have hmpos : (0 : ℝ) < (m : ℝ) := lt_trans hσδ hmδ
  have hm1 : 1 ≤ m := by exact_mod_cast (show 0 < m by exact_mod_cast hmpos)
  have hmesh : (σ - kappa1) / m ≤ δ := by
    rw [div_le_iff₀ hmpos]
    rw [div_lt_iff₀ hδpos] at hmδ
    linarith
  set hh : ℝ := (σ - kappa1) / m with hhh
  have hhpos : 0 < hh := by rw [hhh]; exact div_pos (by linarith) hmpos
  set a : ℕ → ℝ := fun j => kappa1 + (j : ℝ) * hh with haa
  have ha0 : a 0 = kappa1 := by simp only [a]; norm_num
  have ham : a m = σ := by
    simp only [a, hhh]
    field_simp
    ring
  have hmono : Monotone a := by
    intro i j hij
    simp only [a]
    have h1 : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    nlinarith [hhpos]
  have hdelta : ∀ j, a (j + 1) - a j = hh := by
    intro j; simp only [a]; push_cast; ring
  have hale : ∀ j, a j ≤ a (j + 1) := fun j => hmono (Nat.le_succ j)
  have hmem : ∀ j ≤ m, a j ∈ Set.Icc kappa1 σ := by
    intro j hj
    exact ⟨by rw [← ha0]; exact hmono (Nat.zero_le j),
      by rw [← ham]; exact hmono hj⟩
  have hcont : ContinuousOn (fun t : ℝ => Ψ t / t) (Set.Icc kappa1 σ) := by
    refine hΨ.div continuousOn_id ?_
    intro t ht
    exact ne_of_gt (lt_of_lt_of_le hκ1 ht.1)
  have hint : ∀ j < m, IntervalIntegrable (fun t : ℝ => Ψ t / t) MeasureTheory.volume (a j) (a (j + 1)) := by
    intro j hj
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (hale j)]
    refine hcont.mono ?_
    intro t ht
    exact ⟨le_trans (hmem j (by omega)).1 ht.1,
      le_trans ht.2 (hmem (j + 1) (by omega)).2⟩
  have hconstint : ∀ j < m, (∫ t in (a j)..(a (j + 1)), Ψ (a j) / t)
      = Ψ (a j) * (log (a (j + 1)) - log (a j)) := by
    intro j hj
    have hjpos : 0 < a j := lt_of_lt_of_le hκ1 (hmem j (by omega)).1
    have hj1pos : 0 < a (j + 1) := lt_of_lt_of_le hκ1 (hmem (j + 1) (by omega)).1
    have h1 : (∫ t in (a j)..(a (j + 1)), Ψ (a j) / t)
        = Ψ (a j) * ∫ t in (a j)..(a (j + 1)), 1 / t := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      show Ψ (a j) / t = Ψ (a j) * (1 / t)
      rw [mul_one_div]
    rw [h1, _root_.integral_one_div_of_pos hjpos hj1pos,
      Real.log_div (ne_of_gt hj1pos) (ne_of_gt hjpos)]
  have hit : ∀ j < m, IntervalIntegrable (fun t : ℝ => Ψ (a j) / t) MeasureTheory.volume (a j) (a (j + 1)) := by
    intro j hj
    have hjpos : 0 < a j := lt_of_lt_of_le hκ1 (hmem j (by omega)).1
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (hale j)]
    refine continuousOn_const.div continuousOn_id ?_
    intro t ht
    exact ne_of_gt (lt_of_lt_of_le hjpos ht.1)
  have hpiece : ∀ j < m, |(∫ t in (a j)..(a (j + 1)), Ψ t / t) -
      Ψ (a j) * log (a (j + 1) / a j)| ≤ e * log (a (j + 1) / a j) := by
    intro j hj
    have hjpos : 0 < a j := lt_of_lt_of_le hκ1 (hmem j (by omega)).1
    have hj1pos : 0 < a (j + 1) := lt_of_lt_of_le hκ1 (hmem (j + 1) (by omega)).1
    have hAle : a j ≤ a (j + 1) := hale j
    have hdiff : (∫ t in (a j)..(a (j + 1)), Ψ t / t) - Ψ (a j) * log (a (j + 1) / a j)
        = ∫ t in (a j)..(a (j + 1)), (Ψ t - Ψ (a j)) / t := by
      rw [Real.log_div (ne_of_gt hj1pos) (ne_of_gt hjpos), ← hconstint j hj,
        ← intervalIntegral.integral_sub (hint j hj) (hit j hj)]
      apply intervalIntegral.integral_congr
      intro t ht
      show Ψ t / t - Ψ (a j) / t = (Ψ t - Ψ (a j)) / t
      rw [sub_div]
    have hcont1 : IntervalIntegrable (fun t : ℝ => |(Ψ t - Ψ (a j)) / t|) MeasureTheory.volume
        (a j) (a (j + 1)) := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hAle]
      have hc : ContinuousOn (fun t : ℝ => (Ψ t - Ψ (a j)) / t) (Set.Icc kappa1 σ) := by
        refine (hΨ.sub continuousOn_const).div continuousOn_id ?_
        intro t ht
        exact ne_of_gt (lt_of_lt_of_le hκ1 ht.1)
      refine hc.abs.mono ?_
      intro t ht
      exact ⟨le_trans (hmem j (by omega)).1 ht.1,
        le_trans ht.2 (hmem (j + 1) (by omega)).2⟩
    have hcont2 : IntervalIntegrable (fun t : ℝ => e / t) MeasureTheory.volume (a j) (a (j + 1)) := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hAle]
      refine continuousOn_const.div continuousOn_id ?_
      intro t ht
      exact ne_of_gt (lt_of_lt_of_le hjpos ht.1)
    have heconst : (∫ t in (a j)..(a (j + 1)), e / t) = e * log (a (j + 1) / a j) := by
      have h1 : (∫ t in (a j)..(a (j + 1)), e / t)
          = e * ∫ t in (a j)..(a (j + 1)), 1 / t := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t ht
        show e / t = e * (1 / t)
        rw [mul_one_div]
      rw [h1, _root_.integral_one_div_of_pos hjpos hj1pos,
        Real.log_div (ne_of_gt hj1pos) (ne_of_gt hjpos)]
    rw [hdiff]
    calc |∫ t in (a j)..(a (j + 1)), (Ψ t - Ψ (a j)) / t|
        ≤ ∫ t in (a j)..(a (j + 1)), |(Ψ t - Ψ (a j)) / t| :=
          intervalIntegral.abs_integral_le_integral_abs hAle
      _ ≤ ∫ t in (a j)..(a (j + 1)), e / t := by
          apply intervalIntegral.integral_mono_on hAle hcont1 hcont2
          intro t ht
          have htpos : 0 < t := lt_of_lt_of_le hjpos ht.1
          have hd : |Ψ t - Ψ (a j)| ≤ e := by
            have hdt : dist t (a j) ≤ δ := by
              rw [Real.dist_eq]
              have h1 : |t - a j| = t - a j := abs_of_nonneg (by linarith [ht.1])
              rw [h1]
              have h2 : t - a j ≤ a (j + 1) - a j := by linarith [ht.2]
              rw [hdelta j] at h2
              exact le_trans h2 hmesh
            have hmemt : t ∈ Set.Icc kappa1 σ :=
              ⟨le_trans (hmem j (by omega)).1 ht.1,
                le_trans ht.2 (hmem (j + 1) (by omega)).2⟩
            have hres := hδ t hmemt (a j) (hmem j (by omega)) hdt
            rwa [Real.dist_eq] at hres
          rw [abs_div, abs_of_pos htpos]
          exact div_le_div_of_nonneg_right hd (le_of_lt htpos)
      _ = e * log (a (j + 1) / a j) := heconst
  have hsum : |(∫ t in kappa1..σ, Ψ t / t) -
      ∑ j ∈ Finset.range m, Ψ (a j) * log (a (j + 1) / a j)| ≤ e * log (σ / kappa1) := by
    have hpart : (∫ t in kappa1..σ, Ψ t / t) =
        ∑ j ∈ Finset.range m, ∫ t in (a j)..(a (j + 1)), Ψ t / t := by
      rw [← ha0, ← ham]
      exact (intervalIntegral.sum_integral_adjacent_intervals
        (fun j hj => hint j hj)).symm
    rw [hpart, ← Finset.sum_sub_distrib]
    refine le_trans (le_trans (Finset.abs_sum_le_sum_abs _ _)
      (Finset.sum_le_sum (fun j hj => hpiece j (Finset.mem_range.mp hj)))) ?_
    have h2 : (∑ j ∈ Finset.range m, e * log (a (j + 1) / a j)) = e * log (σ / kappa1) := by
      rw [← Finset.mul_sum]
      congr 1
      have hlog : ∀ j, log (a (j + 1) / a j) = log (a (j + 1)) - log (a j) := by
        intro j
        have hjpos : 0 < a j := by
          simp only [a]
          have h0 : (0 : ℝ) ≤ (j : ℝ) * hh := by positivity
          linarith
        have hj1pos : 0 < a (j + 1) := by
          simp only [a]
          push_cast
          have h0 : (0 : ℝ) ≤ ((j : ℝ) + 1) * hh := by positivity
          linarith
        exact Real.log_div (ne_of_gt hj1pos) (ne_of_gt hjpos)
      calc ∑ j ∈ Finset.range m, log (a (j + 1) / a j)
          = ∑ j ∈ Finset.range m, (log (a (j + 1)) - log (a j)) :=
            Finset.sum_congr rfl (fun j _ => hlog j)
        _ = log (a m) - log (a 0) := Finset.sum_range_sub (fun j => log (a j)) m
        _ = log (σ / kappa1) := by
            rw [ham, ha0]
            exact (Real.log_div (ne_of_gt (lt_trans hκ1 hκσ)) (ne_of_gt hκ1)).symm
    rw [h2]
  have hstep : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range m,
      Ψ (a j) * ∑ p ∈ Wu41.PS N ((N : ℝ) ^ a j) ((N : ℝ) ^ a (j + 1)), (1 : ℝ) / (p : ℝ))
      atTop (𝓝 (∑ j ∈ Finset.range m, Ψ (a j) * log (a (j + 1) / a j))) := by
    have key : ∀ j ∈ Finset.range m, Tendsto (fun N : ℕ => Ψ (a j) *
        ∑ p ∈ Wu41.PS N ((N : ℝ) ^ a j) ((N : ℝ) ^ a (j + 1)), (1 : ℝ) / (p : ℝ))
        atTop (𝓝 (Ψ (a j) * log (a (j + 1) / a j))) := by
      intro j hj
      have hj' : j < m := Finset.mem_range.mp hj
      have hajj : 0 < a j := lt_of_lt_of_le hκ1 (hmem j (by omega)).1
      have hajlt : a j < 1 := by
        have h2 : a j < a m := by
          simp only [a]
          have h3 : (j : ℝ) < (m : ℝ) := by exact_mod_cast hj'
          nlinarith [hhpos]
        rw [ham] at h2
        linarith
      exact (b349_ps_mass_tendsto hajj hajlt (hale j)).const_mul (Ψ (a j))
    exact tendsto_finsetSum _ key
  have hband : ∀ᶠ N : ℕ in atTop,
      |(∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
          Ψ (log (p : ℝ) / log N) / (p : ℝ)) -
        (∑ j ∈ Finset.range m, Ψ (a j) *
          ∑ p ∈ Wu41.PS N ((N : ℝ) ^ a j) ((N : ℝ) ^ a (j + 1)), (1 : ℝ) / (p : ℝ))|
      ≤ e * (log (σ / kappa1) + 1) := by
    filter_upwards [hmassb, eventually_ge_atTop (2 : ℕ)] with N hNm hN
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
    have hlogN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
    have hsplit := b349_band_split (σ := σ) N (by omega) hm1 ha0 ham hmono
    have hdisj : ∀ x ∈ Finset.range m, ∀ y ∈ Finset.range m, x ≠ y →
        Disjoint (Wu41.PS N ((N : ℝ) ^ a x) ((N : ℝ) ^ a (x + 1)))
          (Wu41.PS N ((N : ℝ) ^ a y) ((N : ℝ) ^ a (y + 1))) := by
      intro x hx y hy hne
      rw [Finset.disjoint_left]
      intro p hp hp'
      have hp1 : (p : ℝ) < (N : ℝ) ^ a (x + 1) := (Wu41.mem_PS.mp hp).2.2.1
      have hp1' : (p : ℝ) < (N : ℝ) ^ a (y + 1) := (Wu41.mem_PS.mp hp').2.2.1
      have hp2 : (N : ℝ) ^ a y ≤ (p : ℝ) := (Wu41.mem_PS.mp hp').2.1
      have hp2' : (N : ℝ) ^ a x ≤ (p : ℝ) := (Wu41.mem_PS.mp hp).2.1
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : (N : ℝ) ^ a (x + 1) ≤ (N : ℝ) ^ a y :=
          rpow_le_rpow_of_exponent_le hN1 (hmono (by omega))
        linarith
      · have hle : (N : ℝ) ^ a (y + 1) ≤ (N : ℝ) ^ a x :=
          rpow_le_rpow_of_exponent_le hN1 (hmono (by omega))
        linarith
    have hsum_split : (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
        Ψ (log (p : ℝ) / log N) / (p : ℝ))
        = ∑ j ∈ Finset.range m, ∑ p ∈ Wu41.PS N ((N : ℝ) ^ a j) ((N : ℝ) ^ a (j + 1)),
            Ψ (log (p : ℝ) / log N) / (p : ℝ) := by
      rw [hsplit, Finset.sum_biUnion hdisj]
    rw [hsum_split, ← Finset.sum_sub_distrib]
    have h1 : (∑ j ∈ Finset.range m,
        |(∑ p ∈ Wu41.PS N ((N : ℝ) ^ a j) ((N : ℝ) ^ a (j + 1)),
            Ψ (log (p : ℝ) / log N) / (p : ℝ)) -
          Ψ (a j) * ∑ p ∈ Wu41.PS N ((N : ℝ) ^ a j) ((N : ℝ) ^ a (j + 1)),
            (1 : ℝ) / (p : ℝ)|) ≤
        ∑ j ∈ Finset.range m, e * ∑ p ∈ Wu41.PS N ((N : ℝ) ^ a j) ((N : ℝ) ^ a (j + 1)),
            (1 : ℝ) / (p : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j < m := Finset.mem_range.mp hj
      have hajj : 0 < a j := lt_of_lt_of_le hκ1 (hmem j (by omega)).1
      have hEq : (∑ p ∈ Wu41.PS N ((N : ℝ) ^ a j) ((N : ℝ) ^ a (j + 1)),
            Ψ (log (p : ℝ) / log N) / (p : ℝ)) -
          Ψ (a j) * ∑ p ∈ Wu41.PS N ((N : ℝ) ^ a j) ((N : ℝ) ^ a (j + 1)),
            (1 : ℝ) / (p : ℝ)
          = ∑ p ∈ Wu41.PS N ((N : ℝ) ^ a j) ((N : ℝ) ^ a (j + 1)),
              (Ψ (log (p : ℝ) / log N) - Ψ (a j)) / (p : ℝ) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        rw [mul_one_div, sub_div]
      rw [hEq]
      calc |∑ p ∈ Wu41.PS N ((N : ℝ) ^ a j) ((N : ℝ) ^ a (j + 1)),
            (Ψ (log (p : ℝ) / log N) - Ψ (a j)) / (p : ℝ)|
          ≤ ∑ p ∈ Wu41.PS N ((N : ℝ) ^ a j) ((N : ℝ) ^ a (j + 1)),
              |(Ψ (log (p : ℝ) / log N) - Ψ (a j)) / (p : ℝ)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p ∈ Wu41.PS N ((N : ℝ) ^ a j) ((N : ℝ) ^ a (j + 1)), e / (p : ℝ) := by
            apply Finset.sum_le_sum
            intro p hp
            obtain ⟨hpp, hpge, hplt, -⟩ := Wu41.mem_PS.mp hp
            have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
            have hexp : (N : ℝ) ^ a j = Real.exp ((a j) * log (N : ℝ)) := by
              rw [Real.rpow_def_of_pos hNpos]; ring_nf
            have hexp1 : (N : ℝ) ^ a (j + 1) = Real.exp ((a (j + 1)) * log (N : ℝ)) := by
              rw [Real.rpow_def_of_pos hNpos]; ring_nf
            have hlow : (a j) * log (N : ℝ) ≤ log (p : ℝ) := by
              rw [hexp] at hpge
              have h := Real.log_le_log (Real.exp_pos _) hpge
              rwa [Real.log_exp] at h
            have hhigh : log (p : ℝ) < (a (j + 1)) * log (N : ℝ) := by
              rw [hexp1] at hplt
              have h := Real.log_lt_log hppos hplt
              rwa [Real.log_exp] at h
            have htpl : a j ≤ log (p : ℝ) / log (N : ℝ) := by
              rw [le_div_iff₀ hlogN]; linarith
            have htpr : log (p : ℝ) / log (N : ℝ) ≤ a (j + 1) := by
              rw [div_le_iff₀ hlogN]; linarith
            have hmemt : log (p : ℝ) / log (N : ℝ) ∈ Set.Icc kappa1 σ :=
              ⟨le_trans (hmem j (by omega)).1 htpl,
                le_trans htpr (hmem (j + 1) (by omega)).2⟩
            have hdt : dist (log (p : ℝ) / log (N : ℝ)) (a j) ≤ δ := by
              rw [Real.dist_eq]
              have h1 : |log (p : ℝ) / log (N : ℝ) - a j| =
                  log (p : ℝ) / log (N : ℝ) - a j := abs_of_nonneg (by linarith)
              rw [h1]
              have h2 : log (p : ℝ) / log (N : ℝ) - a j ≤ a (j + 1) - a j := by linarith
              rw [hdelta j] at h2
              exact le_trans h2 hmesh
            have hres : |Ψ (log (p : ℝ) / log (N : ℝ)) - Ψ (a j)| ≤ e := by
              have h := hδ _ hmemt (a j) (hmem j (by omega)) hdt
              rwa [Real.dist_eq] at h
            rw [abs_div, abs_of_pos hppos]
            exact div_le_div_of_nonneg_right hres (le_of_lt hppos)
        _ = e * ∑ p ∈ Wu41.PS N ((N : ℝ) ^ a j) ((N : ℝ) ^ a (j + 1)),
            (1 : ℝ) / (p : ℝ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p hp
            rw [mul_one_div]
    refine le_trans (le_trans (Finset.abs_sum_le_sum_abs _ _) h1) ?_
    calc (∑ j ∈ Finset.range m, e *
          ∑ p ∈ Wu41.PS N ((N : ℝ) ^ a j) ((N : ℝ) ^ a (j + 1)), (1 : ℝ) / (p : ℝ))
        = e * ∑ j ∈ Finset.range m,
            ∑ p ∈ Wu41.PS N ((N : ℝ) ^ a j) ((N : ℝ) ^ a (j + 1)), (1 : ℝ) / (p : ℝ) := by
          rw [Finset.mul_sum]
      _ = e * ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ), (1 : ℝ) / (p : ℝ) := by
          rw [hsplit, Finset.sum_biUnion hdisj]
      _ ≤ e * (log (σ / kappa1) + 1) :=
          mul_le_mul_of_nonneg_left hNm (le_of_lt hepos)
  have hstepclose : ∀ᶠ N : ℕ in atTop,
      |(∑ j ∈ Finset.range m, Ψ (a j) *
          ∑ p ∈ Wu41.PS N ((N : ℝ) ^ a j) ((N : ℝ) ^ a (j + 1)), (1 : ℝ) / (p : ℝ)) -
        ∑ j ∈ Finset.range m, Ψ (a j) * log (a (j + 1) / a j)| ≤ e := by
    have h := Metric.tendsto_nhds.mp hstep e hepos
    filter_upwards [h] with N hN
    rw [Real.dist_eq] at hN
    exact le_of_lt hN
  filter_upwards [hband, hstepclose] with N hb hs
  set X : ℝ := ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
    Ψ (log (p : ℝ) / log N) / (p : ℝ) with hX
  set Y : ℝ := ∑ j ∈ Finset.range m, Ψ (a j) *
    ∑ p ∈ Wu41.PS N ((N : ℝ) ^ a j) ((N : ℝ) ^ a (j + 1)), (1 : ℝ) / (p : ℝ) with hY
  set W : ℝ := ∑ j ∈ Finset.range m, Ψ (a j) * log (a (j + 1) / a j) with hW
  set Z : ℝ := ∫ t in kappa1..σ, Ψ t / t with hZ
  have hb' : |X - Y| ≤ e * (log (σ / kappa1) + 1) := by rw [hX, hY]; exact hb
  have hs' : |Y - W| ≤ e := by rw [hY, hW]; exact hs
  have hsum' : |W - Z| ≤ e * log (σ / kappa1) := by
    rw [hW, hZ, abs_sub_comm]
    exact hsum
  rw [Real.dist_eq]
  refine lt_of_le_of_lt (b := e * (log (σ / kappa1) + 1) + e + e * log (σ / kappa1)) ?_ ?_
  · have htri : |X - Z| ≤ |X - Y| + |Y - W| + |W - Z| := by
      have h1 : X - Z = (X - Y) + (Y - W) + (W - Z) := by ring
      rw [h1]
      linarith [abs_add_le ((X - Y) + (Y - W)) (W - Z), abs_add_le (X - Y) (Y - W)]
    linarith
  · have hXe : e * (log (σ / kappa1) + 1) + e + e * log (σ / kappa1)
        = e * (2 * log (σ / kappa1) + 2) := by ring
    rw [hXe, he]
    have h4 : 0 < 4 * (log (σ / kappa1) + 2) := by linarith
    have hId : ε / (4 * (log (σ / kappa1) + 2)) * (2 * log (σ / kappa1) + 2)
        = ε * (2 * log (σ / kappa1) + 2) / (4 * (log (σ / kappa1) + 2)) := by ring
    rw [hId]
    rw [div_lt_iff₀ h4]
    nlinarith

end LeanLab.ChenDoubleSieve.Task349

#print axioms LeanLab.ChenDoubleSieve.Task349.b349_floor_band_mass_tendsto
#print axioms LeanLab.ChenDoubleSieve.Task349.b349_ps_mass_tendsto
#print axioms LeanLab.ChenDoubleSieve.Task349.b349_band_split
#print axioms LeanLab.ChenDoubleSieve.Task349.b349_band_sum_tendsto

namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348
open Wu04Functional (IsLinearSieve IsBuchstab)

/-! ## Pass 2026-11-15T2150Z — the fixed sifting level

The two OPEN leaves are `basic_finite_upper` (needs a linear sieve upper bound, absent from
Mathlib and from this file's closure) and `basic_main_tendsto` (a single statement over
`i ∈ {1,2,3}`).  This pass works on `basic_main_tendsto`, coordinate by coordinate.
`basicMain` at `i ≠ 1` has the sifting level `N ^ kappa1` independent of `p`, so the local
density factors out of the prime sum and `Task348.scaledDensity_tendsto` (proved,
sorry-free, in this file's closure) supplies its limit.
-/

/-- Every coordinate but the first sifts to the fixed lower level. -/
theorem b349_basicSifting_ne_one (N p : ℕ) (i : Fin 12) (hi : i ≠ 1) :
    basicSifting N p i = (N : ℝ) ^ kappa1 := by
  simp only [basicSifting, if_neg hi]

/-- At the fixed level the local density is the module's `lowerDensity`. -/
theorem b349_localDensity_fixed (N : ℕ) :
    Task363.localDensity N ((N : ℝ) ^ kappa1) = Task348.lowerDensity N := rfl

/-- The normalized main term at a fixed sifting level is the scaled density times the
weighted prime sum. -/
theorem b349_basicMain_fixed_ratio (F : ℝ → ℝ) (B : ℝ) {N : ℕ} (hN : 2 ≤ N)
    {i : Fin 12} (hi : i ≠ 1) :
    basicMain F B N i / Θ N = Task348.scaledDensity N *
      ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint i),
        F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) /
          log ((N : ℝ) ^ kappa1)) / ((p : ℝ) - 1) := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < log (N : ℝ) := Real.log_pos hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hCN : 0 < CN N := CN_pos N
  simp only [basicMain, basicSifting, if_neg hi, b349_localDensity_fixed]
  have hsum : (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint i),
      Task348.lowerDensity N / ((p : ℝ) - 1) *
        F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) /
          log ((N : ℝ) ^ kappa1)))
      = Task348.lowerDensity N *
        ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ basicEndpoint i),
          F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) /
            log ((N : ℝ) ^ kappa1)) / ((p : ℝ) - 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hsum, Θ, Task348.scaledDensity]
  field_simp

/-- The logarithmic sieve-level loss tends to zero. -/
theorem b349_loss_tendsto (B : ℝ) :
    Tendsto (fun N : ℕ => B * (log (log (N : ℝ)) / log (N : ℝ))) atTop (𝓝 0) := by
  have hsmall : Tendsto (fun x : ℝ => log x / x) atTop (𝓝 0) := by
    simpa using tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := (hsmall.comp hlog).const_mul B
  simpa using h

/-- The exact form of the `F` argument at a fixed sifting level. -/
theorem b349_arg_eq (B : ℝ) {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p) :
    log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log ((N : ℝ) ^ kappa1)
      = (1 / 2 - log (p : ℝ) / log (N : ℝ)) / kappa1 -
        B * (log (log (N : ℝ)) / log (N : ℝ)) / kappa1 := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < log (N : ℝ) := Real.log_pos hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hzp : (0 : ℝ) < (N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B :=
    div_pos (Real.rpow_pos_of_pos hNpos _) (Real.rpow_pos_of_pos hlog B)
  rw [log_div hzp.ne' hppos.ne', log_div (Real.rpow_pos_of_pos hNpos _).ne'
    (Real.rpow_pos_of_pos hlog B).ne', log_rpow hlog, log_rpow hNpos, log_rpow hNpos]
  field_simp
  ring

/-- The band restricts the logarithmic ratio to the sieve interval. -/
theorem b349_arg_ratio_bounds {N p : ℕ} {σ : ℝ} (hN : 2 ≤ N)
    (hp : p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ)) :
    kappa1 ≤ log (p : ℝ) / log (N : ℝ) ∧ log (p : ℝ) / log (N : ℝ) ≤ σ := by
  obtain ⟨hpp, hge, hlt, -⟩ := Wu41.mem_PS.mp hp
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < log (N : ℝ) := Real.log_pos hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
  have hlo : log ((N : ℝ) ^ kappa1) ≤ log (p : ℝ) :=
    Real.log_le_log (Real.rpow_pos_of_pos hNpos _) hge
  rw [log_rpow hNpos] at hlo
  have hhi : log (p : ℝ) ≤ log ((N : ℝ) ^ σ) := (Real.log_lt_log hppos hlt).le
  rw [log_rpow hNpos] at hhi
  constructor
  · rw [le_div_iff₀ hlog]; linarith
  · rw [div_le_iff₀ hlog]; linarith

/-- A function continuous on the positive axis is bounded on a compact positive interval. -/
theorem b349_bound_of_continuous {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (ha : 0 < a)
    (hF : ContinuousOn F (Set.Ioi 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Set.Icc a b, |F x| ≤ M := by
  have hK : Set.Icc a b ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le ha hx.1
  have hc : ContinuousOn F (Set.Icc a b) := hF.mono hK
  obtain ⟨x, -, hx⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab) hc
  obtain ⟨y, -, hy⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hab) hc
  refine ⟨max |F x| |F y|, by positivity, fun t ht => ?_⟩
  have h1 : F t ≤ F x := hx ht
  have h2 : F y ≤ F t := hy ht
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (F y), le_max_right |F x| |F y|]
  · linarith [le_abs_self (F x), le_max_left |F x| |F y|]

/-- Uniformly convergent weights converge in the band prime sum. -/
theorem b349_band_sum_uniform {σ : ℝ} (hκσ : kappa1 < σ) (hσ1 : σ ≤ 1)
    {Ψ : ℝ → ℝ} (hΨ : ContinuousOn Ψ (Set.Icc kappa1 σ))
    {Ψn : ℕ → ℝ → ℝ}
    (hconv : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ t ∈ Set.Icc kappa1 σ, |Ψn N t - Ψ t| ≤ ε) :
    Tendsto (fun N : ℕ => ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
        Ψn N (log (p : ℝ) / log N) / (p : ℝ)) atTop
      (𝓝 (∫ t in kappa1..σ, Ψ t / t)) := by
  classical
  have hκ1 : 0 < kappa1 := by norm_num [kappa1]
  have hL : 0 < log (σ / kappa1) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hκ1]
    linarith
  have hCpos : 0 < log (σ / kappa1) + 2 := by linarith
  have hbase := b349_band_sum_tendsto hκσ hσ1 Ψ hΨ
  have hmass := b349_ps_mass_tendsto (a := kappa1) (b := σ) hκ1
    (by norm_num [kappa1]) hκσ.le
  have hmassb : ∀ᶠ N : ℕ in atTop,
      (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ), (1 : ℝ) / (p : ℝ)) ≤
        log (σ / kappa1) + 2 :=
    hmass.eventually (eventually_le_nhds (by linarith))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hepos : 0 < ε / (2 * (log (σ / kappa1) + 2)) := by positivity
  have hstep : ∀ᶠ N : ℕ in atTop,
      |(∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
            Ψn N (log (p : ℝ) / log N) / (p : ℝ)) -
          (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
            Ψ (log (p : ℝ) / log N) / (p : ℝ))| ≤ ε / 2 := by
    filter_upwards [hconv (ε / (2 * (log (σ / kappa1) + 2))) hepos, hmassb,
      eventually_ge_atTop 2] with N hun hm hN
    have hsub : (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
          Ψn N (log (p : ℝ) / log N) / (p : ℝ)) -
        (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
          Ψ (log (p : ℝ) / log N) / (p : ℝ))
        = ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
            (Ψn N (log (p : ℝ) / log N) - Ψ (log (p : ℝ) / log N)) / (p : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [hsub]
    have hb : ∀ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
        |(Ψn N (log (p : ℝ) / log N) - Ψ (log (p : ℝ) / log N)) / (p : ℝ)| ≤
          (ε / (2 * (log (σ / kappa1) + 2))) * (1 / (p : ℝ)) := by
      intro p hp
      have hpp := (Wu41.mem_PS.mp hp).1
      have hp2 : (0 : ℝ) < (p : ℝ) := by
        have := hpp.two_le
        exact_mod_cast (show 0 < p by omega)
      have ht := b349_arg_ratio_bounds (σ := σ) hN hp
      have hT := hun (log (p : ℝ) / log N) ⟨ht.1, ht.2⟩
      rw [abs_div, abs_of_pos hp2, div_le_iff₀ hp2]
      have hEq : ε / (2 * (log (σ / kappa1) + 2)) * (1 / (p : ℝ)) * (p : ℝ) =
          ε / (2 * (log (σ / kappa1) + 2)) := by
        field_simp
      rw [hEq]
      exact hT
    calc |∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
            (Ψn N (log (p : ℝ) / log N) - Ψ (log (p : ℝ) / log N)) / (p : ℝ)|
        ≤ ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
            |(Ψn N (log (p : ℝ) / log N) - Ψ (log (p : ℝ) / log N)) / (p : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
            (ε / (2 * (log (σ / kappa1) + 2))) * (1 / (p : ℝ)) := Finset.sum_le_sum hb
      _ = (ε / (2 * (log (σ / kappa1) + 2))) *
            ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ), (1 / (p : ℝ)) := by
          rw [Finset.mul_sum]
      _ ≤ (ε / (2 * (log (σ / kappa1) + 2))) * (log (σ / kappa1) + 2) := by
          apply mul_le_mul_of_nonneg_left hm
          positivity
      _ = ε / 2 := by
          field_simp
  have hb' : ∀ᶠ N : ℕ in atTop,
      dist (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
        Ψ (log (p : ℝ) / log N) / (p : ℝ)) (∫ t in kappa1..σ, Ψ t / t) < ε / 2 :=
    Metric.tendsto_nhds.mp hbase (ε / 2) (by linarith)
  filter_upwards [hstep, hb'] with N hs hb
  rw [Real.dist_eq] at hb ⊢
  have htri : |(∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
        Ψn N (log (p : ℝ) / log N) / (p : ℝ)) - (∫ t in kappa1..σ, Ψ t / t)| ≤
      |(∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
          Ψn N (log (p : ℝ) / log N) / (p : ℝ)) -
        (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
          Ψ (log (p : ℝ) / log N) / (p : ℝ))| +
      |(∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
          Ψ (log (p : ℝ) / log N) / (p : ℝ)) - (∫ t in kappa1..σ, Ψ t / t)| := by
    have hEq : (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
          Ψn N (log (p : ℝ) / log N) / (p : ℝ)) - (∫ t in kappa1..σ, Ψ t / t) =
        ((∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
            Ψn N (log (p : ℝ) / log N) / (p : ℝ)) -
          (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
            Ψ (log (p : ℝ) / log N) / (p : ℝ))) +
        ((∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
            Ψ (log (p : ℝ) / log N) / (p : ℝ)) - (∫ t in kappa1..σ, Ψ t / t)) := by ring
    rw [hEq]
    exact abs_add_le _ _
  linarith


/-- The unshifted `F` argument of `t` lies in the compact positive interval `K`. -/
theorem b349_unshift_mem {σ t : ℝ} (hκ : kappa1 < σ) (ht : t ∈ Set.Icc kappa1 σ) :
    (1 / 2 - t) / kappa1 ∈ Set.Icc ((1 / 2 - σ) / kappa1) ((1 / 2 - kappa1) / kappa1) := by
  have hκ1 : 0 < kappa1 := by norm_num [kappa1]
  constructor
  · have h1 : (1 / 2 - σ) / kappa1 ≤ (1 / 2 - t) / kappa1 :=
      div_le_div_of_nonneg_right (by linarith [ht.2]) hκ1.le
    linarith
  · have h2 : (1 / 2 - t) / kappa1 ≤ (1 / 2 - kappa1) / kappa1 :=
      div_le_div_of_nonneg_right (by linarith [ht.1]) hκ1.le
    linarith

/-- The level-shifted `F` argument of `t` lies in the compact positive interval `K`. -/
theorem b349_shift_mem {σ t c : ℝ} (hκ : kappa1 < σ) (ht : t ∈ Set.Icc kappa1 σ)
    (hc : |c| ≤ kappa1 / 2) :
    (1 / 2 - t) / kappa1 - c / kappa1 ∈
      Set.Icc ((1 / 2 - σ) / kappa1 - 1 / 2) ((1 / 2 - kappa1) / kappa1 + 1 / 2) := by
  obtain ⟨h1, h2⟩ := b349_unshift_mem hκ ht
  have hκ1 : 0 < kappa1 := by norm_num [kappa1]
  have h4 : -(1 / 2 : ℝ) ≤ c / kappa1 := by
    rw [le_div_iff₀ hκ1]
    linarith [neg_abs_le c]
  have h5 : c / kappa1 ≤ 1 / 2 := by
    rw [div_le_iff₀ hκ1]
    linarith [le_abs_self c]
  constructor <;> linarith

/-- The fixed-level weighted prime sum converges to its integral. -/
theorem b349_fixed_sum_tendsto {F : ℝ → ℝ} (hF : ContinuousOn F (Set.Ioi 0)) (B : ℝ)
    (hB : 0 < B) {σ : ℝ} (hκσ : kappa1 < σ) (hσ : σ < 1 / 2 - 2 * kappa1) :
    Tendsto (fun N : ℕ => ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
        F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) /
          log ((N : ℝ) ^ kappa1)) / ((p : ℝ) - 1)) atTop
      (𝓝 (∫ t in kappa1..σ, F ((1 / 2 - t) / kappa1) / t)) := by
  classical
  have hκ1 : 0 < kappa1 := by norm_num [kappa1]
  have hσ1 : σ ≤ 1 := by
    have : (1 / 2 - 2 * kappa1 : ℝ) < 1 := by norm_num [kappa1]
    linarith
  have hKpos : 0 < (1 / 2 - σ) / kappa1 - 1 / 2 := by
    have h1 : (1 / 2 : ℝ) < (1 / 2 - σ) / kappa1 := by
      rw [lt_div_iff₀ hκ1]; linarith
    linarith
  have hKle : (1 / 2 - σ) / kappa1 - 1 / 2 ≤ (1 / 2 - kappa1) / kappa1 + 1 / 2 := by
    have h1 : (1 / 2 - σ) / kappa1 ≤ (1 / 2 - kappa1) / kappa1 :=
      div_le_div_of_nonneg_right (by linarith) hκ1.le
    linarith
  have hKsub : Set.Icc ((1 / 2 - σ) / kappa1 - 1 / 2) ((1 / 2 - kappa1) / kappa1 + 1 / 2) ⊆ Set.Ioi 0 :=
    fun x hx => lt_of_lt_of_le hKpos hx.1
  set Ψ : ℝ → ℝ := fun t => F ((1 / 2 - t) / kappa1) with hΨdef
  set Ψn : ℕ → ℝ → ℝ := fun N t =>
    F ((1 / 2 - t) / kappa1 - B * (log (log (N : ℝ)) / log (N : ℝ)) / kappa1) with hΨndef
  have hmaps : Set.MapsTo (fun t : ℝ => (1 / 2 - t) / kappa1) (Set.Icc kappa1 σ) (Set.Ioi 0) := by
    intro t ht
    show 0 < (1 / 2 - t) / kappa1
    have h := (b349_unshift_mem hκσ ht).1
    linarith
  have hΨcont : ContinuousOn Ψ (Set.Icc kappa1 σ) := by
    have hg : ContinuousOn (fun t : ℝ => (1 / 2 - t) / kappa1) (Set.Icc kappa1 σ) := by fun_prop
    exact hF.comp hg hmaps
  have hsmall : ∀ᶠ N : ℕ in atTop,
      |B * (log (log (N : ℝ)) / log (N : ℝ))| / kappa1 ≤ 1 / 2 := by
    have hlim : Tendsto (fun N : ℕ => |B * (log (log (N : ℝ)) / log (N : ℝ))| / kappa1)
        atTop (𝓝 0) := by
      have h := (b349_loss_tendsto B).abs.div_const kappa1
      simpa using h
    exact hlim.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hconv : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ t ∈ Set.Icc kappa1 σ, |Ψn N t - Ψ t| ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff_le.mp
      (isCompact_Icc.uniformContinuousOn_of_continuous (hF.mono hKsub)) ε hε
    have hlim : Tendsto (fun N : ℕ => |B * (log (log (N : ℝ)) / log (N : ℝ))| / kappa1)
        atTop (𝓝 0) := by
      have h := (b349_loss_tendsto B).abs.div_const kappa1
      simpa using h
    have hc : ∀ᶠ N : ℕ in atTop,
        |B * (log (log (N : ℝ)) / log (N : ℝ))| / kappa1 ≤ min (δ / 2) (1 / 2) :=
      hlim.eventually (eventually_le_nhds (by positivity))
    filter_upwards [hc] with N hN
    intro t ht
    have hc1 : |B * (log (log (N : ℝ)) / log (N : ℝ))| ≤ kappa1 / 2 := by
      have h2 : |B * (log (log (N : ℝ)) / log (N : ℝ))| / kappa1 ≤ 1 / 2 :=
        le_trans hN (min_le_right _ _)
      rw [div_le_iff₀ hκ1] at h2
      linarith
    have hle : |B * (log (log (N : ℝ)) / log (N : ℝ))| / kappa1 ≤ δ := by
      have h2 : |B * (log (log (N : ℝ)) / log (N : ℝ))| / kappa1 ≤ δ / 2 :=
        le_trans hN (min_le_left _ _)
      linarith
    have hdist : dist ((1 / 2 - t) / kappa1 - B * (log (log (N : ℝ)) / log (N : ℝ)) / kappa1)
        ((1 / 2 - t) / kappa1) ≤ δ := by
      rw [Real.dist_eq]
      have h3 : ((1 / 2 - t) / kappa1 - B * (log (log (N : ℝ)) / log (N : ℝ)) / kappa1) -
          ((1 / 2 - t) / kappa1) = -(B * (log (log (N : ℝ)) / log (N : ℝ)) / kappa1) := by ring
      rw [h3, abs_neg, abs_div, abs_of_pos hκ1]
      exact hle
    have hmem : (1 / 2 - t) / kappa1 ∈
        Set.Icc ((1 / 2 - σ) / kappa1 - 1 / 2) ((1 / 2 - kappa1) / kappa1 + 1 / 2) := by
      obtain ⟨h1, h2⟩ := b349_unshift_mem hκσ ht
      exact ⟨by linarith, by linarith⟩
    have hmain := hδ _ (b349_shift_mem hκσ ht hc1) _ hmem hdist
    simpa only [Real.dist_eq, Ψ, Ψn] using hmain
  have hmain := b349_band_sum_uniform hκσ hσ1 hΨcont hconv
  obtain ⟨M, hM0, hM⟩ := b349_bound_of_continuous hKle hKpos hF
  have hmass := b349_ps_mass_tendsto (a := kappa1) (b := σ) hκ1
    (by norm_num [kappa1]) hκσ.le
  have hmassb : ∀ᶠ N : ℕ in atTop,
      (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ), (1 : ℝ) / (p : ℝ)) ≤
        log (σ / kappa1) + 2 :=
    hmass.eventually (eventually_le_nhds (by
      have hL : 0 < log (σ / kappa1) := by
        apply Real.log_pos; rw [lt_div_iff₀ hκ1]; linarith
      linarith))
  have hcorr : Tendsto (fun N : ℕ =>
      (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
          Ψn N (log (p : ℝ) / log N) / ((p : ℝ) - 1)) -
        (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
          Ψn N (log (p : ℝ) / log N) / (p : ℝ))) atTop (𝓝 0) := by
    have hbnd : ∀ᶠ N : ℕ in atTop,
        |(∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
            Ψn N (log (p : ℝ) / log N) / ((p : ℝ) - 1)) -
          (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
            Ψn N (log (p : ℝ) / log N) / (p : ℝ))|
          ≤ (M * (1 / ((N : ℝ) ^ kappa1 - 1))) * (log (σ / kappa1) + 2) := by
      filter_upwards [hmassb, hsmall, eventually_ge_atTop 2] with N hm hcs hN
      have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
      have hNrpow : 1 < (N : ℝ) ^ kappa1 := by
        calc (1 : ℝ) = (1 : ℝ) ^ kappa1 := (Real.one_rpow _).symm
          _ < (N : ℝ) ^ kappa1 := Real.rpow_lt_rpow (by norm_num) hN1 hκ1
      have hden : 0 < (N : ℝ) ^ kappa1 - 1 := by linarith
      have hcle : |B * (log (log (N : ℝ)) / log (N : ℝ))| ≤ kappa1 / 2 := by
        rw [div_le_iff₀ hκ1] at hcs
        linarith
      have hsub : (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
            Ψn N (log (p : ℝ) / log N) / ((p : ℝ) - 1)) -
          (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
            Ψn N (log (p : ℝ) / log N) / (p : ℝ))
          = ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
              Ψn N (log (p : ℝ) / log N) * (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro p _
        field_simp
      rw [hsub]
      have hterm : ∀ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
          |Ψn N (log (p : ℝ) / log N) * (1 / ((p : ℝ) - 1) - 1 / (p : ℝ))|
            ≤ (M * (1 / ((N : ℝ) ^ kappa1 - 1))) * (1 / (p : ℝ)) := by
        intro p hp
        obtain ⟨hpp, hge, hlt, -⟩ := Wu41.mem_PS.mp hp
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
        have hpne : (p : ℝ) ≠ 0 := by linarith
        have hpne' : (p : ℝ) - 1 ≠ 0 := by linarith
        have ht : log (p : ℝ) / log N ∈ Set.Icc kappa1 σ :=
          b349_arg_ratio_bounds (σ := σ) hN hp
        have hMb : |Ψn N (log (p : ℝ) / log N)| ≤ M := hM _ (b349_shift_mem hκσ ht hcle)
        have he : 1 / ((p : ℝ) - 1) - 1 / (p : ℝ) = (1 / ((p : ℝ) - 1)) * (1 / (p : ℝ)) := by
          field_simp
          ring
        have hdiff : 0 ≤ 1 / ((p : ℝ) - 1) - 1 / (p : ℝ) := by
          rw [he]
          exact mul_nonneg (div_nonneg zero_le_one (by linarith))
            (div_nonneg zero_le_one (by linarith))
        have hkey : 1 / ((p : ℝ) - 1) - 1 / (p : ℝ)
            ≤ (1 / ((N : ℝ) ^ kappa1 - 1)) * (1 / (p : ℝ)) := by
          rw [he]
          apply mul_le_mul_of_nonneg_right _ (div_nonneg zero_le_one (by linarith))
          exact one_div_le_one_div_of_le hden (by linarith)
        rw [abs_mul, abs_of_nonneg hdiff]
        calc |Ψn N (log (p : ℝ) / log N)| * (1 / ((p : ℝ) - 1) - 1 / (p : ℝ))
            ≤ M * (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) :=
              mul_le_mul_of_nonneg_right hMb hdiff
          _ ≤ M * ((1 / ((N : ℝ) ^ kappa1 - 1)) * (1 / (p : ℝ))) :=
              mul_le_mul_of_nonneg_left hkey hM0
          _ = (M * (1 / ((N : ℝ) ^ kappa1 - 1))) * (1 / (p : ℝ)) := by ring
      calc |∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
              Ψn N (log (p : ℝ) / log N) * (1 / ((p : ℝ) - 1) - 1 / (p : ℝ))|
          ≤ ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
              |Ψn N (log (p : ℝ) / log N) * (1 / ((p : ℝ) - 1) - 1 / (p : ℝ))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
              (M * (1 / ((N : ℝ) ^ kappa1 - 1))) * (1 / (p : ℝ)) := Finset.sum_le_sum hterm
        _ = (M * (1 / ((N : ℝ) ^ kappa1 - 1))) *
              ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ), (1 / (p : ℝ)) := by
            rw [Finset.mul_sum]
        _ ≤ (M * (1 / ((N : ℝ) ^ kappa1 - 1))) * (log (σ / kappa1) + 2) := by
            apply mul_le_mul_of_nonneg_left hm
            have hpos : 0 < 1 / ((N : ℝ) ^ kappa1 - 1) := by positivity
            exact mul_nonneg hM0 hpos.le
    have hzero : Tendsto (fun N : ℕ =>
        (M * (1 / ((N : ℝ) ^ kappa1 - 1))) * (log (σ / kappa1) + 2)) atTop (𝓝 0) := by
      have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ kappa1) atTop atTop :=
        (tendsto_rpow_atTop hκ1).comp tendsto_natCast_atTop_atTop
      have hsub : Tendsto (fun N : ℕ => (N : ℝ) ^ kappa1 - 1) atTop atTop :=
        tendsto_atTop_add_const_right _ (-1) hpow
      have hinv : Tendsto (fun N : ℕ => 1 / ((N : ℝ) ^ kappa1 - 1)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hsub
      have h2 : Tendsto (fun N : ℕ => (1 / ((N : ℝ) ^ kappa1 - 1)) * (log (σ / kappa1) + 2))
          atTop (𝓝 0) := by
        simpa using hinv.mul_const (log (σ / kappa1) + 2)
      have h3 := h2.const_mul M
      simpa [mul_comm, mul_left_comm, mul_assoc] using h3
    have hlow : ∀ᶠ N : ℕ in atTop,
        -((M * (1 / ((N : ℝ) ^ kappa1 - 1))) * (log (σ / kappa1) + 2)) ≤
          (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
              Ψn N (log (p : ℝ) / log N) / ((p : ℝ) - 1)) -
            (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
              Ψn N (log (p : ℝ) / log N) / (p : ℝ)) := by
      filter_upwards [hbnd] with N hN
      exact (abs_le.mp hN).1
    have hupp : ∀ᶠ N : ℕ in atTop,
        (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
            Ψn N (log (p : ℝ) / log N) / ((p : ℝ) - 1)) -
          (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
            Ψn N (log (p : ℝ) / log N) / (p : ℝ))
          ≤ (M * (1 / ((N : ℝ) ^ kappa1 - 1))) * (log (σ / kappa1) + 2) := by
      filter_upwards [hbnd] with N hN
      exact (abs_le.mp hN).2
    have hneg : Tendsto (fun N : ℕ =>
        -((M * (1 / ((N : ℝ) ^ kappa1 - 1))) * (log (σ / kappa1) + 2))) atTop (𝓝 0) := by
      simpa using hzero.neg
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hzero hlow hupp
  have hsum : Tendsto (fun N : ℕ => ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
      Ψn N (log (p : ℝ) / log N) / ((p : ℝ) - 1)) atTop
      (𝓝 (∫ t in kappa1..σ, Ψ t / t)) := by
    have h := hmain.add hcorr
    simpa using h
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  apply Finset.sum_congr rfl
  intro p hp
  have hpp := (Wu41.mem_PS.mp hp).1
  simp only [hΨndef, b349_arg_eq B hN hpp.pos]

/-- The `t`-integral of the fixed level equals the paper's `u`-integral. -/
theorem b349_fixed_integral_subst (F : ℝ → ℝ) {σ : ℝ} :
    (∫ t in kappa1..σ, F ((1 / 2 - t) / kappa1) / t)
      = 2 * kappa1 * ∫ u in ((1 / 2 - σ) / kappa1)..((1 / 2 - kappa1) / kappa1),
          F u / (1 - 2 * kappa1 * u) := by
  have hκ1 : kappa1 ≠ 0 := by norm_num [kappa1]
  have hu0 : (-kappa1) * ((1 / 2 - σ) / kappa1) + 1 / 2 = σ := by
    field_simp
    ring
  have hu1 : (-kappa1) * ((1 / 2 - kappa1) / kappa1) + 1 / 2 = kappa1 := by
    field_simp
    ring
  have hsub := intervalIntegral.integral_comp_mul_add
    (f := fun t : ℝ => F ((1 / 2 - t) / kappa1) / t)
    (a := (1 / 2 - σ) / kappa1) (b := (1 / 2 - kappa1) / kappa1)
    (show (-kappa1) ≠ 0 by simpa using hκ1) (1 / 2)
  rw [hu0, hu1] at hsub
  have hcongr : (∫ x in (1 / 2 - σ) / kappa1..(1 / 2 - kappa1) / kappa1,
      (fun t : ℝ => F ((1 / 2 - t) / kappa1) / t) ((-kappa1) * x + 1 / 2))
      = ∫ x in (1 / 2 - σ) / kappa1..(1 / 2 - kappa1) / kappa1,
          2 * (F x / (1 - 2 * kappa1 * x)) := by
    apply intervalIntegral.integral_congr
    intro x _
    show F ((1 / 2 - ((-kappa1) * x + 1 / 2)) / kappa1) / ((-kappa1) * x + 1 / 2)
        = 2 * (F x / (1 - 2 * kappa1 * x))
    have h1 : (1 / 2 : ℝ) - ((-kappa1) * x + 1 / 2) = kappa1 * x := by ring
    have h2 : (-kappa1) * x + 1 / 2 = 1 / 2 - kappa1 * x := by ring
    rw [h1, h2, mul_div_cancel_left₀ x hκ1]
    field_simp
  rw [hcongr, intervalIntegral.integral_const_mul] at hsub
  have hsym : (∫ x in σ..kappa1, F ((1 / 2 - x) / kappa1) / x)
      = -(∫ x in kappa1..σ, F ((1 / 2 - x) / kappa1) / x) := by
    have h := intervalIntegral.integral_symm
      (μ := MeasureTheory.volume) (f := fun x : ℝ => F ((1 / 2 - x) / kappa1) / x) (a := kappa1) (b := σ)
    linarith [h]
  rw [hsym] at hsub
  have hsmul : (-kappa1)⁻¹ • (-(∫ x in kappa1..σ, F ((1 / 2 - x) / kappa1) / x))
      = (∫ x in kappa1..σ, F ((1 / 2 - x) / kappa1) / x) / kappa1 := by
    rw [smul_eq_mul]
    field_simp
  rw [hsmul] at hsub
  rw [eq_div_iff hκ1] at hsub
  rw [← hsub]
  ring

/-- The scaled density times the fixed-level prime sum has the paper's limit. -/
theorem b349_fixed_main_tendsto (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (B : ℝ)
    (hB : 0 < B) {σ : ℝ} (hκσ : kappa1 < σ) (hσ : σ < 1 / 2 - 2 * kappa1) :
    Tendsto (fun N : ℕ => Task348.scaledDensity N *
        ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
          F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) /
            log ((N : ℝ) ^ kappa1)) / ((p : ℝ) - 1)) Task348.evenAtTop
      (𝓝 ((4 / exp eulerMascheroniConstant) *
        ∫ u in ((1 / 2 - σ) / kappa1)..((1 / 2 - kappa1) / kappa1),
          F u / (1 - 2 * kappa1 * u))) := by
  have hsum := (b349_fixed_sum_tendsto h.1 B hB hκσ hσ).mono_left
    (show atTop ⊓ principal {N : ℕ | Even N} ≤ atTop from inf_le_left)
  have hmul := Task348.scaledDensity_tendsto.mul hsum
  have hval : (2 / (kappa1 * exp eulerMascheroniConstant)) *
      (∫ t in kappa1..σ, F ((1 / 2 - t) / kappa1) / t) =
      (4 / exp eulerMascheroniConstant) *
        ∫ u in ((1 / 2 - σ) / kappa1)..((1 / 2 - kappa1) / kappa1),
          F u / (1 - 2 * kappa1 * u) := by
    rw [b349_fixed_integral_subst F]
    have hκ1 : kappa1 ≠ 0 := by norm_num [kappa1]
    have he : exp eulerMascheroniConstant ≠ 0 := (exp_pos _).ne'
    field_simp
    ring
  rw [hval] at hmul
  exact hmul

/-- Coordinate two of `basic_main_tendsto`. -/
theorem b349_basicMain_two_tendsto (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (B : ℝ)
    (hB : 0 < B) :
    Tendsto (fun N : ℕ => basicMain F B N 2 / Θ N) Task348.evenAtTop
      (𝓝 (integralTerms F f ω 2)) := by
  have hgen := b349_fixed_main_tendsto F f ω h B hB
    (σ := sigma1) (by norm_num [kappa1, sigma1]) (by norm_num [kappa1, sigma1])
  have hbend : basicEndpoint (2 : Fin 12) = sigma1 := by
    unfold basicEndpoint
    rw [if_neg (by decide), if_pos rfl]
  have hratio : (fun N : ℕ => basicMain F B N 2 / Θ N) =ᶠ[Task348.evenAtTop]
      (fun N => Task348.scaledDensity N *
        ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ sigma1),
          F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) /
            log ((N : ℝ) ^ kappa1)) / ((p : ℝ) - 1)) := by
    filter_upwards [(eventually_ge_atTop 2).filter_mono inf_le_left] with N hN
    have hb := b349_basicMain_fixed_ratio F B hN (i := (2 : Fin 12)) (by decide)
    rw [hbend] at hb
    exact hb
  have hgoal := Tendsto.congr' hratio.symm hgen
  have hlim : (4 / exp eulerMascheroniConstant) *
      (∫ u in ((1 / 2 - sigma1) / kappa1)..((1 / 2 - kappa1) / kappa1),
        F u / (1 - 2 * kappa1 * u)) = integralTerms F f ω 2 := by
    simp only [integralTerms]
    norm_num
  rw [hlim] at hgoal
  exact hgoal

/-- Coordinate three of `basic_main_tendsto`. -/
theorem b349_basicMain_three_tendsto (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (B : ℝ)
    (hB : 0 < B) :
    Tendsto (fun N : ℕ => basicMain F B N 3 / Θ N) Task348.evenAtTop
      (𝓝 (integralTerms F f ω 3)) := by
  have hgen := b349_fixed_main_tendsto F f ω h B hB
    (σ := sigma2) (by norm_num [kappa1, sigma2]) (by norm_num [kappa1, sigma2])
  have hbend : basicEndpoint (3 : Fin 12) = sigma2 := by
    unfold basicEndpoint
    rw [if_neg (by decide), if_neg (by decide)]
  have hratio : (fun N : ℕ => basicMain F B N 3 / Θ N) =ᶠ[Task348.evenAtTop]
      (fun N => Task348.scaledDensity N *
        ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ sigma2),
          F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) /
            log ((N : ℝ) ^ kappa1)) / ((p : ℝ) - 1)) := by
    filter_upwards [(eventually_ge_atTop 2).filter_mono inf_le_left] with N hN
    have hb := b349_basicMain_fixed_ratio F B hN (i := (3 : Fin 12)) (by decide)
    rw [hbend] at hb
    exact hb
  have hgoal := Tendsto.congr' hratio.symm hgen
  have hlim : (4 / exp eulerMascheroniConstant) *
      (∫ u in ((1 / 2 - sigma2) / kappa1)..((1 / 2 - kappa1) / kappa1),
        F u / (1 - 2 * kappa1 * u)) = integralTerms F f ω 3 := by
    simp only [integralTerms]
    norm_num
  rw [hlim] at hgoal
  exact hgoal

end LeanLab.ChenDoubleSieve.Task349

namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348
open Wu04Functional (IsLinearSieve IsBuchstab)

/-! ## Pass 2026-11-19T00:45Z — the variable (first) sifting level

`basicMain` at `i = 1` sifts with level `p` itself and carries the weight
`log p * localDensity N p / CN N`.  The prime sum therefore has the reciprocal
totient weight `1 / (p - 1)` rather than `1 / p`, and a *variable* coefficient.
This block supplies both: the `1 / (p - 1)` band sum, then the coefficient.
-/

/-- Logarithmic coordinates of a `PS` band element. -/
theorem b349_band_log_mem {a b : ℝ} {N p : ℕ} (hN : 2 ≤ N)
    (hp : p ∈ Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b)) :
    log (p : ℝ) / log (N : ℝ) ∈ Icc a b := by
  obtain ⟨hpp, hpa, hpb, -⟩ := Wu41.mem_PS.mp hp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hpa' : a * log (N : ℝ) ≤ log (p : ℝ) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hNpos a) hpa
    rwa [Real.log_rpow hNpos] at h
  have hpb' : log (p : ℝ) ≤ b * log (N : ℝ) := by
    have h := Real.log_le_log hp0 hpb.le
    rwa [Real.log_rpow hNpos] at h
  exact ⟨(le_div_iff₀ hlN).2 hpa', (div_le_iff₀ hlN).2 hpb'⟩

/-- The reciprocal square prime mass over a band above `N ^ a` vanishes. -/
theorem b349_band_recip_sq_tendsto {a b : ℝ} (ha : 0 < a) (ha1 : a < 1) (hab : a ≤ b) :
    Tendsto (fun N : ℕ => ∑ p ∈ Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b),
      (1 : ℝ) / (p : ℝ) ^ 2) atTop (𝓝 0) := by
  have hmass := b349_ps_mass_tendsto ha ha1 hab
  have hbound : ∀ᶠ N : ℕ in atTop,
      (∑ p ∈ Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b), (1 : ℝ) / (p : ℝ)) ≤
        log (b / a) + 1 :=
    hmass.eventually (eventually_le_nhds (by linarith))
  have hz : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hzinv : Tendsto (fun N : ℕ => ((N : ℝ) ^ a)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hz
  have hzero : Tendsto (fun N : ℕ => ((N : ℝ) ^ a)⁻¹ * (log (b / a) + 1)) atTop (𝓝 0) := by
    simpa using hzinv.mul_const (log (b / a) + 1)
  have hnn : ∀ N : ℕ, 0 ≤ ∑ p ∈ Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b),
      (1 : ℝ) / (p : ℝ) ^ 2 := by
    intro N
    exact Finset.sum_nonneg (fun p hp => by positivity)
  apply squeeze_zero' (Eventually.of_forall hnn) _ hzero
  filter_upwards [hbound, eventually_ge_atTop (2 : ℕ)] with N hb hN
  calc (∑ p ∈ Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b), (1 : ℝ) / (p : ℝ) ^ 2)
      ≤ ∑ p ∈ Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b),
          ((N : ℝ) ^ a)⁻¹ * (1 / (p : ℝ)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpp := (Wu41.mem_PS.mp hp).1
        have hpa := (Wu41.mem_PS.mp hp).2.1
        have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
        have hNapos : (0 : ℝ) < (N : ℝ) ^ a := Real.rpow_pos_of_pos hNpos a
        have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
        have hinv : (1 : ℝ) / (p : ℝ) ≤ ((N : ℝ) ^ a)⁻¹ := by
          rw [one_div]
          exact (inv_le_inv₀ hp0 hNapos).2 hpa
        calc (1 : ℝ) / (p : ℝ) ^ 2 = (1 / (p : ℝ)) * (1 / (p : ℝ)) := by ring
          _ ≤ ((N : ℝ) ^ a)⁻¹ * (1 / (p : ℝ)) :=
            mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = ((N : ℝ) ^ a)⁻¹ * ∑ p ∈ Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b),
          (1 / (p : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ ((N : ℝ) ^ a)⁻¹ * (log (b / a) + 1) :=
        mul_le_mul_of_nonneg_left hb (by positivity)

/-- The band reciprocal-totient mass tends to the same logarithmic ratio. -/
theorem b349_ps_mass_recip_tendsto {a b : ℝ} (ha : 0 < a) (ha1 : a < 1) (hab : a ≤ b) :
    Tendsto (fun N : ℕ => ∑ p ∈ Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b),
      (1 : ℝ) / ((p : ℝ) - 1)) atTop (𝓝 (log (b / a))) := by
  have hmass := b349_ps_mass_tendsto ha ha1 hab
  have hsq := b349_band_recip_sq_tendsto ha ha1 hab
  have hnn : ∀ N : ℕ, 0 ≤ ∑ p ∈ Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b),
      ((1 : ℝ) / ((p : ℝ) - 1) - 1 / (p : ℝ)) := by
    intro N
    apply Finset.sum_nonneg
    intro p hp
    have hpp := (Wu41.mem_PS.mp hp).1
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have h2 : (0 : ℝ) < (p : ℝ) := by linarith
    have hkey : (1 : ℝ) / ((p : ℝ) - 1) - 1 / (p : ℝ) =
        1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      field_simp
      ring
    rw [hkey]
    positivity
  have hterm : ∀ N : ℕ, (∑ p ∈ Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b),
      ((1 : ℝ) / ((p : ℝ) - 1) - 1 / (p : ℝ))) ≤
      (2 : ℝ) * ∑ p ∈ Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b), (1 / (p : ℝ) ^ 2) := by
    intro N
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Wu41.mem_PS.mp hp).1
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hkey : (1 : ℝ) / ((p : ℝ) - 1) - 1 / (p : ℝ) =
        1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      field_simp
      ring
    rw [hkey]
    have hstep : (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 / ((p : ℝ) ^ 2 / 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    calc (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 / ((p : ℝ) ^ 2 / 2) := hstep
      _ = 2 * (1 / (p : ℝ) ^ 2) := by field_simp; try ring
  have herr : Tendsto (fun N : ℕ => ∑ p ∈ Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b),
      ((1 : ℝ) / ((p : ℝ) - 1) - 1 / (p : ℝ))) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall hnn) (Eventually.of_forall hterm)
      (by simpa using hsq.const_mul 2)
  have heq : ∀ N : ℕ, (∑ p ∈ Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b),
      (1 : ℝ) / ((p : ℝ) - 1)) =
      (∑ p ∈ Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b), (1 : ℝ) / (p : ℝ)) +
      (∑ p ∈ Wu41.PS N ((N : ℝ) ^ a) ((N : ℝ) ^ b),
        ((1 : ℝ) / ((p : ℝ) - 1) - 1 / (p : ℝ))) := by
    intro N
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have h := hmass.add herr
  rw [add_zero] at h
  exact h.congr' (Eventually.of_forall fun N => (heq N).symm)

/-- A continuous weight is uniformly bounded on the exact band. -/
theorem b349_weight_bound {Ψ : ℝ → ℝ} {σ : ℝ} (hΨ : ContinuousOn Ψ (Set.Icc kappa1 σ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Set.Icc kappa1 σ, |Ψ t| ≤ K := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hΨ
  exact ⟨max C 0, le_max_right _ _, fun t ht => by
    have h := hC t ht
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)⟩

/-- Reciprocal totient prime averaging over the full first band. -/
theorem b349_band_sum_recip_tendsto {σ : ℝ} (hκσ : kappa1 < σ) (hσ1 : σ ≤ 1)
    (Ψ : ℝ → ℝ) (hΨ : ContinuousOn Ψ (Set.Icc kappa1 σ)) :
    Tendsto (fun N : ℕ => ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
        Ψ (log (p : ℝ) / log N) / ((p : ℝ) - 1)) atTop
      (𝓝 (∫ t in kappa1..σ, Ψ t / t)) := by
  have hfix := b349_band_sum_tendsto hκσ hσ1 Ψ hΨ
  obtain ⟨K, hK, hKb⟩ := b349_weight_bound hΨ
  have hsq := b349_band_recip_sq_tendsto (a := kappa1) (b := σ)
    (by norm_num [kappa1]) (by norm_num [kappa1]) hκσ.le
  have hterm : ∀ᶠ N : ℕ in atTop,
      (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
        |Ψ (log (p : ℝ) / log N) * ((1 : ℝ) / ((p : ℝ) - 1) - 1 / (p : ℝ))|) ≤
      (2 * K) * ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ), (1 / (p : ℝ) ^ 2) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Wu41.mem_PS.mp hp).1
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have ht := b349_band_log_mem (a := kappa1) (b := σ) hN hp
    have hΨb : |Ψ (log (p : ℝ) / log N)| ≤ K := hKb _ ht
    have hdiff : |(1 : ℝ) / ((p : ℝ) - 1) - 1 / (p : ℝ)| ≤ 2 / (p : ℝ) ^ 2 := by
      have hkey : (1 : ℝ) / ((p : ℝ) - 1) - 1 / (p : ℝ) =
          1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
        field_simp
        ring
      rw [hkey, abs_of_pos (by positivity : (0 : ℝ) < 1 / ((p : ℝ) * ((p : ℝ) - 1)))]
      have hstep : (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 / ((p : ℝ) ^ 2 / 2) := by
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      calc (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 / ((p : ℝ) ^ 2 / 2) := hstep
        _ = 2 / (p : ℝ) ^ 2 := by field_simp; try ring
    rw [abs_mul]
    calc |Ψ (log (p : ℝ) / log N)| * |(1 : ℝ) / ((p : ℝ) - 1) - 1 / (p : ℝ)|
        ≤ K * (2 / (p : ℝ) ^ 2) :=
          mul_le_mul hΨb hdiff (abs_nonneg _) hK
      _ = (2 * K) * (1 / (p : ℝ) ^ 2) := by ring
  have herr : Tendsto (fun N : ℕ => ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
      Ψ (log (p : ℝ) / log N) * ((1 : ℝ) / ((p : ℝ) - 1) - 1 / (p : ℝ))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun N => abs_nonneg _)) _
      (by simpa using hsq.const_mul (2 * K))
    exact hterm.mono (fun N hN => by
      simpa only [one_div] using le_trans (abs_sum_le_sum_abs _ _) hN)
  have heq : ∀ N : ℕ, (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
      Ψ (log (p : ℝ) / log N) / ((p : ℝ) - 1)) =
      (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
        Ψ (log (p : ℝ) / log N) / (p : ℝ)) +
      (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ σ),
        Ψ (log (p : ℝ) / log N) * ((1 : ℝ) / ((p : ℝ) - 1) - 1 / (p : ℝ))) := by
    intro N
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have h := hfix.add herr
  rw [add_zero] at h
  exact h.congr' (Eventually.of_forall fun N => (heq N).symm)

end LeanLab.ChenDoubleSieve.Task349

namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348

/-! ## Pass 2026-11-19T01:00Z — uniform density normalization above the lower band

Port of the downstream `Decomp349i` / `Decomp349j` argument, rebuilt inside this
file's own import closure.  The two Euler products (`variableSmall` / `variableTail` of the
downstream file) are written out inline because a new `def` is forbidden here.
-/

/-- The singular correction from odd prime divisors at or above a real cutoff is at least one. -/
theorem b349v_tail_one_le (N : ℕ) (z : ℝ) :
    1 ≤ ∏ p ∈ N.primeFactors.filter (fun p : ℕ => 2 < p ∧ z ≤ (p : ℝ)),
      (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  apply Finset.one_le_prod₀
  intro p hp
  have hp2 : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1
  apply (le_div_iff₀ (by linarith)).2
  linarith

/-- All cutoffs above the lower band endpoint are dominated by the existing tail bound. -/
theorem b349v_tail_le {N : ℕ} {z : ℝ} (hz : (N : ℝ) ^ kappa1 ≤ z) :
    (∏ p ∈ N.primeFactors.filter (fun p : ℕ => 2 < p ∧ z ≤ (p : ℝ)),
      (((p : ℝ) - 1) / ((p : ℝ) - 2))) ≤ tailCorrection N := by
  apply Finset.prod_le_prod_of_subset_of_one_le₀
  · intro p hp
    obtain ⟨hpN, hp2, hpz⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hpN, hp2, hz.trans hpz⟩
  · intro p hp
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1
    exact div_nonneg (by linarith) (by linarith)
  · intro p hp _
    have hp2 : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1
    apply (le_div_iff₀ (by linarith)).2
    linarith

/-- The singular factor partitions at every real cutoff. -/
theorem b349v_partition (N : ℕ) (z : ℝ) :
    oddFactor N =
      (∏ p ∈ N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (p : ℝ) < z),
        (((p : ℝ) - 1) / ((p : ℝ) - 2))) *
      (∏ p ∈ N.primeFactors.filter (fun p : ℕ => 2 < p ∧ z ≤ (p : ℝ)),
        (((p : ℝ) - 1) / ((p : ℝ) - 2))) := by
  have he := Finset.prod_filter_mul_prod_filter_not
    (s := N.primeFactors.filter (fun p : ℕ => 2 < p))
    (p := fun p : ℕ => (p : ℝ) < z)
    (f := fun p : ℕ => ((p : ℝ) - 1) / ((p : ℝ) - 2))
  simpa only [Finset.filter_filter, not_lt, oddFactor] using he.symm

/-- The good odd primes at a variable cutoff are exactly the sieve primes. -/
theorem b349v_good_set {N : ℕ} (hEven : Even N) (z : ℝ) :
    Wu41.PS N 0 z = (Wu41.PS 1 3 z).filter (fun p => p.Coprime N) := by
  ext p
  simp only [Finset.mem_filter, Wu41.mem_PS]
  constructor
  · rintro ⟨hp, _, hpz, hcop⟩
    have hp2 : p ≠ 2 := by
      intro heq
      subst p
      exact (Nat.prime_two.coprime_iff_not_dvd.mp hcop) hEven.two_dvd
    exact ⟨⟨hp, by exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega), hpz,
      by simp⟩, hcop⟩
  · rintro ⟨⟨hp, hp3, hpz, _⟩, hcop⟩
    exact ⟨hp, by positivity, hpz, hcop⟩

/-- The omitted odd primes are exactly the prime divisors below the cutoff. -/
theorem b349v_bad_set {N : ℕ} (hN : 2 ≤ N) (z : ℝ) :
    (Wu41.PS 1 3 z).filter (fun p => ¬ p.Coprime N) =
      N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (p : ℝ) < z) := by
  ext p
  simp only [Finset.mem_filter, Wu41.mem_PS, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hp, hp3, hpz, _⟩, hbad⟩
    have hdvd : p ∣ N := by simpa only [hp.coprime_iff_not_dvd, not_not] using hbad
    exact ⟨⟨hp, hdvd, by omega⟩, by exact_mod_cast hp3, hpz⟩
  · rintro ⟨⟨hp, hdvd, _⟩, hp2, hpz⟩
    refine ⟨⟨hp, ?_, hpz, by simp⟩, ?_⟩
    · exact_mod_cast (show 3 ≤ p by omega)
    · exact fun hc => (hp.coprime_iff_not_dvd.mp hc) hdvd

/-- At modulus two the density is exactly the ordinary odd prime product. -/
theorem b349v_ordinaryDensity_product (z : ℝ) :
    Task363.localDensity 2 z =
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ 2 < p),
        (1 - 1 / ((p : ℝ) - 1)) := by
  have hs : Wu41.PS 1 3 z =
      (range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ 2 < p) := by
    ext p
    simp only [Wu41.mem_PS, Finset.mem_filter, Finset.mem_range, Nat.lt_ceil]
    constructor
    · rintro ⟨hp, hp3, hpz, _⟩
      exact ⟨hpz, hp, by exact_mod_cast hp3⟩
    · rintro ⟨hpz, hp, hp2⟩
      exact ⟨hp, by exact_mod_cast (show 3 ≤ p by omega), hpz, by simp⟩
  have hf : (Wu41.PS 1 3 z).filter (fun p => p.Coprime 2) = Wu41.PS 1 3 z := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    have hm := Wu41.mem_PS.mp hp
    have hp3 : 3 ≤ p := by exact_mod_cast hm.2.1
    exact hm.1.coprime_iff_not_dvd.mpr (fun h => by
      have := Nat.le_of_dvd (by norm_num : 0 < 2) h
      omega)
  unfold Task363.localDensity
  rw [b349v_good_set (by norm_num : Even (2 : ℕ)), hf, hs]

/-- The ordinary real cutoff density has the exact Mertens normalization. -/
theorem b349v_ordinaryDensity_tendsto :
    Tendsto (fun z : ℝ => log z * Task363.localDensity 2 z / LeanLab.ChenExplicit.twinC)
      atTop (𝓝 (2 / exp eulerMascheroniConstant)) := by
  have hm := LeanLab.AlmostPrimeSums.Decomp1527c.chen_odd_product_limit_of_mertens
    LeanLab.AlmostPrimeSums.Decomp1527c.mertens_euler_product
  have ht := hm.const_mul (2 / exp eulerMascheroniConstant)
  simp only [mul_one] at ht
  apply ht.congr
  intro z
  rw [b349v_ordinaryDensity_product, exp_neg]
  field_simp [Real.exp_ne_zero, LeanLab.ChenExplicit.twinC_pos.ne']
  <;> ring

/-- The variable local product is the ordinary odd product times its small correction. -/
theorem b349v_density_factor {N : ℕ} (hN : 2 ≤ N) (hEven : Even N) (z : ℝ) :
    Task363.localDensity N z = Task363.localDensity 2 z *
      (∏ p ∈ N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (p : ℝ) < z),
        (((p : ℝ) - 1) / ((p : ℝ) - 2))) := by
  let S := N.primeFactors.filter (fun p : ℕ => 2 < p ∧ (p : ℝ) < z)
  let VB := ∏ p ∈ S, (((p : ℝ) - 1) / ((p : ℝ) - 2))
  let g := fun p : ℕ => 1 - 1 / ((p : ℝ) - 1)
  have hb := Finset.prod_filter_mul_prod_filter_not
    (s := Wu41.PS 1 3 z) (p := fun p => p.Coprime N) (f := g)
  rw [← b349v_good_set hEven, b349v_bad_set hN] at hb
  have hbase : (∏ p ∈ Wu41.PS 1 3 z, g p) = Task363.localDensity 2 z := by
    rw [b349v_ordinaryDensity_product]
    apply Finset.prod_congr
    · ext p
      simp only [Wu41.mem_PS, Finset.mem_filter, Finset.mem_range, Nat.lt_ceil]
      constructor
      · rintro ⟨hp, hp3, hpz, _⟩
        exact ⟨hpz, hp, by exact_mod_cast hp3⟩
      · rintro ⟨hpz, hp, hp2⟩
        exact ⟨hp, by exact_mod_cast (show 3 ≤ p by omega), hpz, by simp⟩
    · intro p hp
      rfl
  change Task363.localDensity N z * (∏ p ∈ S, g p) = _ at hb
  rw [hbase] at hb
  have hc : (∏ p ∈ S, g p) * VB = 1 := by
    change (∏ p ∈ S, g p) * (∏ p ∈ S, ((p : ℝ) - 1) / ((p : ℝ) - 2)) = 1
    rw [← Finset.prod_mul_distrib]
    have he : (∏ p ∈ S, g p * (((p : ℝ) - 1) / ((p : ℝ) - 2))) = ∏ _p ∈ S, (1 : ℝ) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp2 : (2 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.1
      dsimp [g]
      field_simp [show (p : ℝ) - 1 ≠ 0 by linarith, show (p : ℝ) - 2 ≠ 0 by linarith]
      <;> ring
    rw [he]
    simp
  calc
    Task363.localDensity N z = Task363.localDensity N z * 1 := by ring
    _ = Task363.localDensity N z * ((∏ p ∈ S, g p) * VB) := by rw [hc]
    _ = Task363.localDensity 2 z * VB := by rw [← mul_assoc, hb]

/-- The full singular factor cancels after retaining the variable prime tail. -/
theorem b349v_density_tail_factor {N : ℕ} (hN : 2 ≤ N) (hEven : Even N) (z : ℝ) :
    Task363.localDensity N z *
      (∏ p ∈ N.primeFactors.filter (fun p : ℕ => 2 < p ∧ z ≤ (p : ℝ)),
        (((p : ℝ) - 1) / ((p : ℝ) - 2))) = Task363.localDensity 2 z * oddFactor N := by
  rw [b349v_density_factor hN hEven, b349v_partition N z]
  ring

/-- The variable density normalization has an exact ordinary product quotient. -/
theorem b349v_density_normalization {N : ℕ} (hN : 2 ≤ N) (hEven : Even N) (z : ℝ) :
    (log z * Task363.localDensity N z / CN N) *
      (∏ p ∈ N.primeFactors.filter (fun p : ℕ => 2 < p ∧ z ≤ (p : ℝ)),
        (((p : ℝ) - 1) / ((p : ℝ) - 2))) =
      log z * Task363.localDensity 2 z / LeanLab.ChenExplicit.twinC := by
  have ho : oddFactor N ≠ 0 := by have := oddFactor_one_le N; linarith
  calc
    _ = log z * (Task363.localDensity N z *
        (∏ p ∈ N.primeFactors.filter (fun p : ℕ => 2 < p ∧ z ≤ (p : ℝ)),
          (((p : ℝ) - 1) / ((p : ℝ) - 2)))) /
        (oddFactor N * LeanLab.ChenExplicit.twinC) := by unfold CN; ring
    _ = log z * (Task363.localDensity 2 z * oddFactor N) /
        (oddFactor N * LeanLab.ChenExplicit.twinC) := by rw [b349v_density_tail_factor hN hEven]
    _ = _ := by field_simp

/-- Uniform Mertens normalization for all sifting cutoffs above the lower band. -/
theorem b349v_density_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N → ∀ z : ℝ,
      (N : ℝ) ^ kappa1 ≤ z →
      |log z * Task363.localDensity N z / CN N -
        2 / exp eulerMascheroniConstant| ≤ ε := by
  let c : ℝ := 2 / exp eulerMascheroniConstant
  let TAIL : ℕ → ℝ → ℝ := fun N z =>
    ∏ p ∈ N.primeFactors.filter (fun p : ℕ => 2 < p ∧ z ≤ (p : ℝ)),
      (((p : ℝ) - 1) / ((p : ℝ) - 2))
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨Z, hZ⟩ := Metric.tendsto_atTop.1 b349v_ordinaryDensity_tendsto (ε / 2) (by positivity)
  have htail : ∀ᶠ N : ℕ in atTop, |tailCorrection N - 1| < ε / (2 * c) := by
    have ht := tailCorrection_tendsto.eventually
      (Metric.ball_mem_nhds (1 : ℝ) (by positivity : 0 < ε / (2 * c)))
    simpa only [Metric.mem_ball, Real.dist_eq] using ht
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ kappa1) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num [kappa1])).comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ N : ℕ in atTop, ∀ hEven : Even N, ∀ z : ℝ,
      (N : ℝ) ^ kappa1 ≤ z →
      |log z * Task363.localDensity N z / CN N - c| ≤ ε := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), hpow.eventually_ge_atTop Z, htail]
      with N hN hNZ hNt
    intro hEven z hz
    have ha : |log z * Task363.localDensity 2 z / LeanLab.ChenExplicit.twinC - c| < ε / 2 := by
      simpa only [Real.dist_eq] using hZ z (hNZ.trans hz)
    let x := log z * Task363.localDensity N z / CN N
    let t := TAIL N z
    have ht1 : 1 ≤ t := b349v_tail_one_le N z
    have htbound : t ≤ tailCorrection N := b349v_tail_le hz
    have htdiff : 0 ≤ t - 1 := by linarith
    have htdiff' : t - 1 < ε / (2 * c) := by
      have habs : tailCorrection N - 1 ≤ |tailCorrection N - 1| := le_abs_self _
      linarith
    have hprod : x * t = log z * Task363.localDensity 2 z / LeanLab.ChenExplicit.twinC :=
      b349v_density_normalization hN hEven z
    have habs : |x - c| ≤ |x * t - c| + c * (t - 1) := by
      calc
        |x - c| ≤ |x - c| * t := le_mul_of_one_le_right (abs_nonneg _) ht1
        _ = |(x - c) * t| := by rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ t)]
        _ = |(x * t - c) - c * (t - 1)| := by congr 1; ring
        _ ≤ |x * t - c| + |c * (t - 1)| := abs_sub _ _
        _ = |x * t - c| + c * (t - 1) := by rw [abs_of_nonneg (mul_nonneg hc.le htdiff)]
    rw [hprod] at habs
    have hsmall : c * (t - 1) < ε / 2 := by
      have hh := mul_lt_mul_of_pos_left htdiff' hc
      have hid : c * (ε / (2 * c)) = ε / 2 := by field_simp
      rw [hid] at hh
      exact hh
    change |x - c| ≤ ε
    linarith
  obtain ⟨M, hM⟩ := eventually_atTop.1 hevent
  exact ⟨M, fun N hEven hN z hz => hM N hN hEven z hz⟩

/-- Every even modulus cutoff sequence above the lower endpoint has the same normalization. -/
theorem b349v_density_sequence (z : ℕ → ℝ)
    (hz : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ kappa1 ≤ z N) :
    Tendsto (fun N : ℕ => log (z N) * Task363.localDensity N (z N) / CN N)
      evenAtTop (𝓝 (2 / exp eulerMascheroniConstant)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨M, hM⟩ := b349v_density_uniform (ε / 2) (by positivity)
  change ∀ᶠ N in atTop ⊓ principal {N : ℕ | Even N}, _
  rw [eventually_inf_principal]
  filter_upwards [eventually_ge_atTop M, hz] with N hN hzN hEven
  rw [Real.dist_eq]
  exact (hM N hEven hN (z N) hzN).trans_lt (by linarith)

end LeanLab.ChenDoubleSieve.Task349

namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348
open Wu04Functional (IsLinearSieve IsBuchstab)

/-! ## Pass 2026-11-19T01:40Z — coordinate one of `basic_main_tendsto`

`basicMain F B N 1` is `(N / log N) * Σ_p V_N(p)/(p-1) * F(level B N p)` where the
sifting level is `p` itself.  After division by `Θ N` the prime sum carries the
weight `log N * V_N(p) / C_N`, which the uniform density normalization drives to
`c / t_p` with `t_p = log p / log N`, and the loss free level is `1/(2 t_p) - 1`.
-/

/-- The loss free variable level is the reciprocal prime coordinate. -/
theorem b349v_level_zero {N : ℕ} (hN : 2 ≤ N) {p : ℕ} (hp : p.Prime) :
    log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) / log (p : ℝ) =
      1 / (2 * (log (p : ℝ) / log (N : ℝ))) - 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlogN : log (N : ℝ) ≠ 0 := (log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have hlogp : log (p : ℝ) ≠ 0 := (log_pos (by exact_mod_cast hp.one_lt)).ne'
  rw [Real.rpow_zero, div_one, log_div (Real.rpow_pos_of_pos hNpos _).ne' hp0.ne',
    Real.log_rpow hNpos]
  field_simp

/-- The loss free variable level stays between three and five on the full band. -/
theorem b349v_level_zero_range {N : ℕ} (hN : 2 ≤ N) {p : ℕ}
    (hp : p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2)) :
    log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) / log (p : ℝ) ∈
      Icc (3 : ℝ) 5 := by
  rw [b349v_level_zero hN (Wu41.mem_PS.mp hp).1]
  have ht := b349_band_log_mem hN hp
  have htpos : 0 < log (p : ℝ) / log (N : ℝ) := by
    have hk : 0 < kappa1 := by norm_num [kappa1]
    linarith [ht.1]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]
    norm_num [kappa2] at ht
    linarith [ht.2]
  · rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
    norm_num [kappa1] at ht
    linarith [ht.1]

/-- The B dependent level differs from the loss free one by a vanishing logarithmic term. -/
theorem b349v_level_shift_le {B : ℝ} (hB : 0 < B) {N : ℕ} (hN : 2 ≤ N) {p : ℕ}
    (hp : p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2)) :
    |log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ) -
      log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) / log (p : ℝ)|
      ≤ B * |log (log (N : ℝ))| / (kappa1 * log (N : ℝ)) := by
  obtain ⟨hpp, hpa, hpb, -⟩ := Wu41.mem_PS.mp hp
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
  have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hpp.one_lt)
  have hpos : (0 : ℝ) < (N : ℝ) ^ (1 / 2 : ℝ) / (p : ℝ) := by positivity
  have h1 : ((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ) =
      ((N : ℝ) ^ (1 / 2 : ℝ) / (p : ℝ)) / (log N) ^ B := by ring
  have h2 : ((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ) =
      (N : ℝ) ^ (1 / 2 : ℝ) / (p : ℝ) := by rw [Real.rpow_zero, div_one]
  rw [h1, h2, Real.log_div hpos.ne' (Real.rpow_pos_of_pos hlN B).ne', Real.log_rpow hlN]
  have h3 : (log ((N : ℝ) ^ (1 / 2 : ℝ) / (p : ℝ)) - B * log (log (N : ℝ))) / log (p : ℝ) -
      log ((N : ℝ) ^ (1 / 2 : ℝ) / (p : ℝ)) / log (p : ℝ) =
      (-B * log (log (N : ℝ))) / log (p : ℝ) := by
    rw [div_sub_div_same]
    ring
  rw [h3, abs_div, abs_mul, abs_neg, abs_of_pos hB, abs_of_pos hlp]
  rw [div_le_div_iff₀ hlp (mul_pos (by norm_num [kappa1]) hlN)]
  exact mul_le_mul_of_nonneg_left ((le_div_iff₀ hlN).1 (b349_band_log_mem hN hp).1)
    (by positivity)

/-- The level shift vanishes uniformly. -/
theorem b349v_level_shift_zero (B : ℝ) (hB : 0 < B) :
    Tendsto (fun N : ℕ => B * |log (log (N : ℝ))| / (kappa1 * log (N : ℝ)))
      atTop (𝓝 0) := by
  have hbase : Tendsto (fun u : ℝ => log u / u) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hcomp : Tendsto (fun N : ℕ => log (log (N : ℝ)) / log (N : ℝ)) atTop (𝓝 0) :=
    hbase.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have habs : Tendsto (fun N : ℕ => |log (log (N : ℝ)) / log (N : ℝ)|) atTop (𝓝 0) := by
    simpa using hcomp.abs
  have h1 : Tendsto (fun N : ℕ => (B / kappa1) * |log (log (N : ℝ)) / log (N : ℝ)|)
      atTop (𝓝 0) := by
    simpa using habs.const_mul (B / kappa1)
  apply h1.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [abs_div, abs_of_pos hl]
  field_simp

/-- The actual band logarithmic coordinates lie in the printed interval. -/
theorem b349v_arg_mem {t : ℝ} (ht : t ∈ Icc kappa1 kappa2) :
    1 / (2 * t) - 1 ∈ Icc (3 : ℝ) 5 := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num [kappa1]) ht.1
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]
    norm_num [kappa2] at ht
    linarith [ht.2]
  · rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
    norm_num [kappa1] at ht
    linarith [ht.1]

/-- The variable sieve values lose their logarithmic perturbation uniformly. -/
theorem b349v_values_shift_small (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∀ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2),
        |F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ)) -
          F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) /
            log (p : ℝ))| ≤ ε := by
  have hc : ContinuousOn F (Icc (2 : ℝ) 6) := h.1.mono (by
    intro u hu
    change 0 < u
    linarith [hu.1])
  obtain ⟨δ, hδ, hcont⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hc) ε hε
  have hnear : ∀ᶠ N : ℕ in atTop,
      B * |log (log (N : ℝ))| / (kappa1 * log (N : ℝ)) < min 1 δ :=
    (b349v_level_shift_zero B hB).eventually (eventually_lt_nhds (lt_min (by norm_num) hδ))
  obtain ⟨M, hM⟩ := eventually_atTop.1 hnear
  refine ⟨max 2 M, ?_⟩
  intro N hN p hp
  have hN2 : 2 ≤ N := by omega
  have hr := b349v_level_zero_range hN2 hp
  have hd0 := b349v_level_shift_le (B := B) hB hN2 hp
  have hdl : |log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ) -
      log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) / log (p : ℝ)| <
      min 1 δ := lt_of_le_of_lt hd0 (hM N (by omega))
  have hlt1 := hdl.trans_le (min_le_left (1 : ℝ) δ)
  have hltδ := hdl.trans_le (min_le_right (1 : ℝ) δ)
  have hdiff := abs_lt.1 hlt1
  have hzero : log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) / log (p : ℝ) ∈
      Icc (2 : ℝ) 6 := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hBm : log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ) ∈
      Icc (2 : ℝ) 6 :=
    ⟨by linarith [hr.1, hdiff.1], by linarith [hr.2, hdiff.2]⟩
  exact (hcont _ hBm _ hzero (by simpa only [Real.dist_eq] using hltδ)).le

/-- The variable band sieve values are uniformly bounded. -/
theorem b349v_values_bounded (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) :
    ∃ M : ℝ, 0 < M ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∀ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2),
        |F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ))| ≤ M := by
  have hc : ContinuousOn F (Icc (2 : ℝ) 6) := h.1.mono (by
    intro u hu
    change 0 < u
    linarith [hu.1])
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  obtain ⟨J, hJ⟩ := b349v_values_shift_small F f h B hB 1 (by norm_num)
  refine ⟨max C 0 + 1, by positivity, max 2 J, ?_⟩
  intro N hN p hp
  have hN2 : 2 ≤ N := by omega
  have hr := b349v_level_zero_range hN2 hp
  have hb := hC _ (show log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) /
      log (p : ℝ) ∈ Icc (2 : ℝ) 6 from ⟨by linarith [hr.1], by linarith [hr.2]⟩)
  rw [Real.norm_eq_abs] at hb
  calc |F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ))| ≤
      |F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ)) -
        F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) / log (p : ℝ))| +
      |F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) / log (p : ℝ))| := by
        have hh := abs_add_le
          (F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ)) -
            F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) / log (p : ℝ)))
          (F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) / log (p : ℝ)))
        simpa only [sub_add_cancel] using hh
    _ ≤ 1 + C := add_le_add (hJ N (by omega) p hp) hb
    _ ≤ max C 0 + 1 := by linarith [le_max_left C 0]

/-- Exact factorization of the first ordinary main term. -/
theorem b349v_ratio (F : ℝ → ℝ) (B : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    basicMain F B N 1 / Θ N =
      ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2),
        (log (N : ℝ) * Task363.localDensity N p / CN N) *
          F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ)) /
            ((p : ℝ) - 1) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hscal : (N : ℝ) / log N / (CN N * N / (log N) ^ 2) = log (N : ℝ) / CN N := by
    field_simp
  set S : ℝ := ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2),
      Task363.localDensity N p / ((p : ℝ) - 1) *
        F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ)) with hS
  have hform : basicMain F B N 1 / Θ N =
      ((N : ℝ) / log N / (CN N * N / (log N) ^ 2)) * S := by
    simp only [basicMain, basicEndpoint, basicSifting, Θ, ↓reduceIte, hS]
    ring
  rw [hform, hscal, hS, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- The reciprocal totient mass of the first band is uniformly bounded. -/
theorem b349v_mass_bounded : ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2),
      (1 : ℝ) / ((p : ℝ) - 1)) ≤ K := by
  have hlim := b349_ps_mass_recip_tendsto (a := kappa1) (b := kappa2)
    (by norm_num [kappa1]) (by norm_num [kappa1]) (by norm_num [kappa1, kappa2])
  have hev : ∀ᶠ N : ℕ in atTop,
      (∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2),
        (1 : ℝ) / ((p : ℝ) - 1)) ≤ log (kappa2 / kappa1) + 1 :=
    hlim.eventually (eventually_le_nhds (by linarith))
  obtain ⟨M, hM⟩ := eventually_atTop.1 hev
  exact ⟨max (log (kappa2 / kappa1) + 1) 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _),
    max 2 M, fun N hN => (hM N (by omega)).trans (le_max_left _ _)⟩

/-- The first ordinary main term is uniformly close to its loss free prime average. -/
theorem b349v_approx (F f : ℝ → ℝ) (h : IsLinearSieve F f) (B : ℝ) (hB : 0 < B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      |basicMain F B N 1 / Θ N -
        ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2),
          (2 / exp eulerMascheroniConstant) / (log (p : ℝ) / log N) *
            F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) /
              log (p : ℝ)) / ((p : ℝ) - 1)| ≤ ε := by
  obtain ⟨K, hK, MK, hMK⟩ := b349v_mass_bounded
  obtain ⟨M, hM, MM, hMM⟩ := b349v_values_bounded F f h B hB
  let c : ℝ := 2 / exp eulerMascheroniConstant
  have hc : 0 < c := by dsimp [c]; positivity
  let η : ℝ := ε * kappa1 / (K * (M + c))
  have hk : 0 < kappa1 := by norm_num [kappa1]
  have hMKp : 0 < M + c := by linarith
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨D, hD⟩ := b349v_density_uniform η hη
  obtain ⟨S, hS⟩ := b349v_values_shift_small F f h B hB η hη
  refine ⟨max 2 (max MK (max MM (max D S))), ?_⟩
  intro N hEven hN
  have hN2 : 2 ≤ N := by omega
  have hlN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [b349v_ratio F B hN2, ← Finset.sum_sub_distrib]
  calc |∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2),
        ((log (N : ℝ) * Task363.localDensity N p / CN N) *
          F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ)) /
            ((p : ℝ) - 1) -
        c / (log (p : ℝ) / log N) *
          F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) / log (p : ℝ)) /
            ((p : ℝ) - 1))|
      ≤ ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2),
          |((log (N : ℝ) * Task363.localDensity N p / CN N) *
            F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ)) /
              ((p : ℝ) - 1) -
            c / (log (p : ℝ) / log N) *
              F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) /
                log (p : ℝ)) / ((p : ℝ) - 1))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2),
          (η * (M + c) / kappa1) * (1 / ((p : ℝ) - 1)) := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hpp, hpa, hpb, -⟩ := Wu41.mem_PS.mp hp
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
        have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
        have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
        have hlp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hpp.one_lt)
        have htκ : kappa1 ≤ log (p : ℝ) / log (N : ℝ) := (b349_band_log_mem hN2 hp).1
        have htpos : 0 < log (p : ℝ) / log (N : ℝ) := lt_of_lt_of_le hk htκ
        have hAb : |log (p : ℝ) * Task363.localDensity N p / CN N - c| ≤ η := by
          have := hD N hEven (by omega) (p : ℝ) hpa
          convert this using 2
        have hFB : |F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) /
            log (p : ℝ))| ≤ M := hMM N (by omega) p hp
        have hsh : |F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) /
            log (p : ℝ)) -
            F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) /
              log (p : ℝ))| ≤ η :=
          hS N (by omega) p hp
        have hnum : |log (p : ℝ) * Task363.localDensity N p / CN N *
              F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ)) -
            c * F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) /
              log (p : ℝ))| ≤ η * (M + c) := by
          have hsplit : log (p : ℝ) * Task363.localDensity N p / CN N *
                F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ)) -
              c * F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) /
                log (p : ℝ)) =
              (log (p : ℝ) * Task363.localDensity N p / CN N - c) *
                F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ)) +
              c * (F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ)) -
                F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) /
                  log (p : ℝ))) := by ring
          rw [hsplit]
          calc |(log (p : ℝ) * Task363.localDensity N p / CN N - c) *
                  F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ)) +
                c * (F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ)) -
                  F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) /
                    log (p : ℝ)))|
              ≤ |(log (p : ℝ) * Task363.localDensity N p / CN N - c) *
                  F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ))| +
                |c * (F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ)) -
                  F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) /
                    log (p : ℝ)))| := abs_add_le _ _
            _ = |log (p : ℝ) * Task363.localDensity N p / CN N - c| *
                  |F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ))| +
                c * |F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ)) -
                  F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) /
                    log (p : ℝ))| := by rw [abs_mul, abs_mul, abs_of_pos hc]
            _ ≤ η * M + c * η :=
              add_le_add (mul_le_mul hAb hFB (abs_nonneg _) hη.le)
                (mul_le_mul_of_nonneg_left hsh hc.le)
            _ = η * (M + c) := by ring
        have heq : (log (N : ℝ) * Task363.localDensity N p / CN N) *
              F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ)) /
                ((p : ℝ) - 1) -
              c / (log (p : ℝ) / log N) *
                F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) /
                  log (p : ℝ)) / ((p : ℝ) - 1) =
              (log (p : ℝ) * Task363.localDensity N p / CN N *
                  F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ)) -
                c * F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) /
                  log (p : ℝ))) / (log (p : ℝ) / log N) / ((p : ℝ) - 1) := by
          have hlogN : log (N : ℝ) = log (p : ℝ) / (log (p : ℝ) / log (N : ℝ)) := by
            field_simp
          rw [hlogN]
          field_simp
        rw [heq, abs_div, abs_div, abs_of_pos htpos, abs_of_pos hp1]
        calc (|log (p : ℝ) * Task363.localDensity N p / CN N *
              F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (p : ℝ)) / log (p : ℝ)) -
            c * F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) /
              log (p : ℝ))| / (log (p : ℝ) / log N)) / ((p : ℝ) - 1)
            ≤ (η * (M + c) / (log (p : ℝ) / log N)) / ((p : ℝ) - 1) :=
              div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hnum htpos.le) hp1.le
          _ ≤ (η * (M + c) / kappa1) / ((p : ℝ) - 1) :=
              div_le_div_of_nonneg_right
                (div_le_div_of_nonneg_left (by positivity) hk htκ) hp1.le
          _ = (η * (M + c) / kappa1) * (1 / ((p : ℝ) - 1)) := by ring
    _ = (η * (M + c) / kappa1) *
        ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2),
          (1 / ((p : ℝ) - 1)) := by rw [Finset.mul_sum]
    _ ≤ (η * (M + c) / kappa1) * K :=
        mul_le_mul_of_nonneg_left (hMK N (by omega)) (by positivity)
    _ = ε := by
        have hη : η = ε * kappa1 / (K * (M + c)) := rfl
        rw [hη]
        have hKp : K ≠ 0 := by linarith
        have hMp : M + c ≠ 0 := by linarith
        have hkg : kappa1 ≠ 0 := by norm_num [kappa1]
        field_simp
        try ring

end LeanLab.ChenDoubleSieve.Task349

namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348
open Wu04Functional (IsLinearSieve IsBuchstab)

/-! ## Pass 2026-11-19T02:10Z — the limit of coordinate one -/

/-- The variable weight `c F(1/(2t)-1)/t` is continuous on the exact band. -/
theorem b349v_weight_continuous (F : ℝ → ℝ) (hF : ContinuousOn F (Ioi (0 : ℝ))) :
    ContinuousOn (fun t : ℝ => (2 / exp eulerMascheroniConstant) * F (1 / (2 * t) - 1) / t)
      (Set.Icc kappa1 kappa2) := by
  have hk1 : 0 < kappa1 := by norm_num [kappa1]
  have htpos : ∀ t ∈ Set.Icc kappa1 kappa2, 0 < t := fun t ht => lt_of_lt_of_le hk1 ht.1
  have harg : ContinuousOn (fun t : ℝ => 1 / (2 * t) - 1) (Set.Icc kappa1 kappa2) := by
    fun_prop (disch := intro t ht; have := htpos t ht; positivity)
  have hFc : ContinuousOn (fun t : ℝ => F (1 / (2 * t) - 1)) (Set.Icc kappa1 kappa2) :=
    hF.comp harg (fun t ht => by
      have h := b349v_arg_mem ht
      exact lt_of_lt_of_le (by norm_num) h.1)
  exact (continuousOn_const.mul hFc).div continuousOn_id (fun t ht => (htpos t ht).ne')

/-- The loss free prime average of coordinate one has its exact integral limit. -/
theorem b349v_T_tendsto (F : ℝ → ℝ) (hF : ContinuousOn F (Ioi (0 : ℝ))) :
    Tendsto (fun N : ℕ => ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2),
        (2 / exp eulerMascheroniConstant) / (log (p : ℝ) / log N) *
          F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) /
            log (p : ℝ)) / ((p : ℝ) - 1)) atTop
      (𝓝 ((2 / exp eulerMascheroniConstant) *
        ∫ t in kappa1..kappa2, F (1 / (2 * t) - 1) / t ^ 2)) := by
  have hκ : kappa1 < kappa2 := by norm_num [kappa1, kappa2]
  have hΨc : ContinuousOn
      (fun t : ℝ => (2 / exp eulerMascheroniConstant) * F (1 / (2 * t) - 1) / t)
      (Set.Icc kappa1 kappa2) := b349v_weight_continuous F hF
  have hband := b349_band_sum_recip_tendsto (σ := kappa2) hκ (by norm_num [kappa2])
    (fun t : ℝ => (2 / exp eulerMascheroniConstant) * F (1 / (2 * t) - 1) / t) hΨc
  have hsum : (fun N : ℕ => ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2),
        (2 / exp eulerMascheroniConstant) / (log (p : ℝ) / log N) *
          F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) /
            log (p : ℝ)) / ((p : ℝ) - 1)) =ᶠ[atTop]
      (fun N : ℕ => ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2),
        ((2 / exp eulerMascheroniConstant) * F (1 / (2 * (log (p : ℝ) / log N)) - 1) /
          (log (p : ℝ) / log N)) / ((p : ℝ) - 1)) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    apply Finset.sum_congr rfl
    intro p hp
    have hpp := (Wu41.mem_PS.mp hp).1
    rw [b349v_level_zero hN hpp]
    ring
  have hint : (∫ t in kappa1..kappa2,
      ((2 / exp eulerMascheroniConstant) * F (1 / (2 * t) - 1) / t) / t) =
      (2 / exp eulerMascheroniConstant) *
        ∫ t in kappa1..kappa2, F (1 / (2 * t) - 1) / t ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  rw [hint] at hband
  exact hband.congr' hsum.symm

/-- The reciprocal coordinate substitution for the first upper integral. -/
theorem b349v_kernel_integral (F : ℝ → ℝ) (hF : ContinuousOn F (Ioi (0 : ℝ))) :
    (∫ t in kappa1..kappa2, F (1 / (2 * t) - 1) / t ^ 2) =
      2 * ∫ u in (1 / (2 * kappa2) - 1)..(1 / (2 * kappa1) - 1), F u := by
  let g : ℝ → ℝ := fun t => 1 / (2 * t) - 1
  let g' : ℝ → ℝ := fun t => -1 / (2 * t ^ 2)
  have hkle : kappa1 ≤ kappa2 := by norm_num [kappa1, kappa2]
  have htpos : ∀ t ∈ Set.uIcc kappa1 kappa2, 0 < t := by
    intro t ht
    rw [Set.uIcc_of_le hkle] at ht
    exact lt_of_lt_of_le (by norm_num [kappa1]) ht.1
  have hd : ∀ t ∈ Set.uIcc kappa1 kappa2, HasDerivAt g (g' t) t := by
    intro t ht
    have ht0 := (htpos t ht).ne'
    have h2t : 2 * t ≠ 0 := mul_ne_zero (by norm_num) ht0
    have hraw := ((hasDerivAt_const t (1 : ℝ)).div ((hasDerivAt_id t).const_mul 2) h2t).sub_const 1
    convert hraw using 1 <;> dsimp [g, g'] <;> field_simp <;> ring
  have hdc : ContinuousOn g' (Set.uIcc kappa1 kappa2) := by
    dsimp [g']
    fun_prop (disch := intro t ht; have := htpos t ht; positivity)
  have hFi : ContinuousOn F (g '' Set.uIcc kappa1 kappa2) := hF.mono (by
    rintro u ⟨t, ht, rfl⟩
    rw [Set.uIcc_of_le hkle] at ht
    have hr := b349v_arg_mem ht
    exact lt_of_lt_of_le (by norm_num) hr.1)
  have he := intervalIntegral.integral_comp_mul_deriv' hd hdc hFi
  calc (∫ t in kappa1..kappa2, F (1 / (2 * t) - 1) / t ^ 2)
      = (-2) * ∫ t in kappa1..kappa2, (F ∘ g) t * g' t := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t ht
        have ht0 : t ≠ 0 := (htpos t ht).ne'
        dsimp [g, g']
        field_simp
        try ring
    _ = (-2) * ∫ u in g kappa1..g kappa2, F u := by rw [he]
    _ = 2 * ∫ u in g kappa2..g kappa1, F u := by
        rw [intervalIntegral.integral_symm (a := g kappa1) (b := g kappa2)]
        ring
    _ = _ := rfl

/-- Coordinate one of `basic_main_tendsto`. -/
theorem b349v_one_tendsto (F f ω : ℝ → ℝ) (h : IsLinearSieve F f) (B : ℝ) (hB : 0 < B) :
    Tendsto (fun N : ℕ => basicMain F B N 1 / Θ N) evenAtTop
      (𝓝 (integralTerms F f ω 1)) := by
  have hdiff : Tendsto (fun N : ℕ => basicMain F B N 1 / Θ N -
      ∑ p ∈ Wu41.PS N ((N : ℝ) ^ kappa1) ((N : ℝ) ^ kappa2),
        (2 / exp eulerMascheroniConstant) / (log (p : ℝ) / log N) *
          F (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ (0 : ℝ)) / (p : ℝ)) /
            log (p : ℝ)) / ((p : ℝ) - 1)) evenAtTop (𝓝 0) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    obtain ⟨M, hM⟩ := b349v_approx F f h B hB (ε / 2) (by positivity)
    change ∀ᶠ N in atTop ⊓ principal {N : ℕ | Even N}, _
    rw [eventually_inf_principal]
    filter_upwards [eventually_ge_atTop M] with N hN hEven
    simpa only [Real.dist_eq, sub_zero] using (hM N hEven hN).trans_lt (by linarith)
  have hT := tendsto_inf_left (x₂ := principal {N : ℕ | Even N}) (b349v_T_tendsto F h.1)
  have hsum := hdiff.add hT
  have hlim : (0 : ℝ) + (2 / exp eulerMascheroniConstant) *
      (∫ t in kappa1..kappa2, F (1 / (2 * t) - 1) / t ^ 2) = integralTerms F f ω 1 := by
    rw [zero_add, b349v_kernel_integral F h.1]
    simp only [integralTerms]
    norm_num
    try ring
  rw [hlim] at hsum
  simpa only [Pi.sub_apply, Pi.add_apply, sub_add_cancel] using hsum

/-- LEAF. Wu 2004 page 39, display before 10.3 and the same sieve step for 10.4.
Only the count to finite prime sum comparison is asserted.
The passage from li N to N over log N is included in the error. -/
theorem basic_finite_upper (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        ∀ i : Fin 12, i ∈ ({1, 2, 3} : Finset (Fin 12)) →
          sieveTerms N i ≤ basicMain F B N i + η * Θ N := by
  sorry

/-- LEAF. Wu 2004 page 39, replacement of the prime sums in 10.3 and 10.4.
This has no actual sieve count. It includes product normalization,
prime partial summation and removal of the finite logarithmic level loss. -/
theorem basic_main_tendsto (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) :
    ∀ i : Fin 12, i ∈ ({1, 2, 3} : Finset (Fin 12)) →
      Tendsto (fun N => basicMain F B N i / Θ N) evenAtTop
        (𝓝 (integralTerms F f ω i)) := by
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  · exact b349v_one_tendsto F f ω h B hB
  · exact b349_basicMain_two_tendsto F f ω h B hB
  · exact b349_basicMain_three_tendsto F f ω h B hB

/-- An upper count estimate follows from a finite main term and its limit.
This is the elementary final normalization used on pages 39 to 41. -/
theorem upper_of_main (c : ℝ) (u : ℕ → ℝ) (main : ℝ → ℕ → ℝ)
    (hsieve : ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N → u N ≤ main B N + η * Θ N)
    (hlimit : ∀ B : ℝ, 0 < B →
      Tendsto (fun N => main B N / Θ N) evenAtTop (𝓝 c)) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      u N ≤ (c + ε) * Θ N := by
  intro ε hε
  obtain ⟨B, hB, M, hM⟩ := hsieve (ε / 2) (by positivity)
  have he : ∀ᶠ N in evenAtTop, main B N / Θ N < c + ε / 2 :=
    (hlimit B hB).eventually (eventually_lt_nhds (by linarith : c < c + ε / 2))
  obtain ⟨K, hK⟩ := eventually_atTop.1 (eventually_inf_principal.1 he)
  refine ⟨max 2 (max M K), ?_⟩
  intro N hEven hN
  have ht := Θ_pos (show 2 ≤ N by omega)
  have hc := (div_lt_iff₀ ht).1 (hK N (by omega) hEven)
  have hs := hM N hEven (by omega)
  nlinarith

/-- Finitely many separate thresholds give one threshold for the whole group. -/
theorem finite_upper_threshold (I : Finset (Fin 12)) (u : ℕ → Fin 12 → ℝ)
    (c : Fin 12 → ℝ)
    (h : ∀ i ∈ I, ∀ ε : ℝ, 0 < ε → ∃ M : ℕ,
      ∀ N : ℕ, Even N → M ≤ N → u N i ≤ (c i + ε) * Θ N) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ N : ℕ, Even N → M ≤ N →
      ∀ i ∈ I, u N i ≤ (c i + ε) * Θ N := by
  intro ε hε
  have he : ∀ i ∈ I, ∀ᶠ N in evenAtTop, u N i ≤ (c i + ε) * Θ N := by
    intro i hi
    obtain ⟨M, hM⟩ := h i hi ε hε
    exact eventually_inf_principal.2 (eventually_atTop.2
      ⟨M, fun N hN hEven => hM N hEven hN⟩)
  have hall := I.eventually_all.2 he
  obtain ⟨M, hM⟩ := eventually_atTop.1 (eventually_inf_principal.1 hall)
  exact ⟨M, fun N hEven hN => hM N hN hEven⟩

/-- The exact sealed basic_upper conclusion from two strictly smaller leaves.
OPEN through basic_finite_upper and basic_main_tendsto. -/
theorem basic_upper_supplied (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({1, 2, 3} : Finset (Fin 12)) →
        sieveTerms N i ≤ (integralTerms F f ω i + ε) * Θ N := by
  apply finite_upper_threshold
  intro i hi
  apply upper_of_main _ _ (fun B N => basicMain F B N i)
  · intro η hη
    obtain ⟨B, hB, M, hM⟩ := basic_finite_upper F f h η hη
    exact ⟨B, hB, M, fun N hEven hN => hM N hEven hN i hi⟩
  · exact fun B hB => basic_main_tendsto F f ω h B hB i hi

end LeanLab.ChenDoubleSieve.Task349
