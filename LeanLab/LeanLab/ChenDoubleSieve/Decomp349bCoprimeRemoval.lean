import LeanLab.ChenDoubleSieve.Decomp349bSplitSum

/-!
Proof of the LEAF `leaf_coprime_removal` of Decomp349bSplitSum, Wu 2004 page 41,
removal of the coprimality condition in display 10.9. Source: https://arxiv.org/pdf/0705.1652.
The pairs of `freePairs` not in `switchedPairs` have a prime dividing N; both primes
are at least N to kappa2, the weight log N over log of N over p q is at most 3, and
N has at most log N over log 2 prime factors, so the difference is O of log N squared
over N to kappa2.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348

/-- The prime reciprocal sum up to N is at most 1 plus log N, by the harmonic bound. -/
theorem bc_prime_recip_le (N : ℕ) :
    ∑ q ∈ (Finset.range (N + 1)).filter Nat.Prime, (1 : ℝ) / q ≤ 1 + log N := by
  have h1 : ∑ q ∈ (Finset.range (N + 1)).filter Nat.Prime, (1 : ℝ) / q ≤
      ∑ q ∈ Finset.range (N + 1), (1 : ℝ) / q :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => by positivity)
  have h2 : ∑ q ∈ Finset.range (N + 1), (1 : ℝ) / q = ((harmonic N : ℚ) : ℝ) := by
    rw [Finset.sum_range_succ', harmonic]
    push_cast
    simp [one_div]
  have h3 : ((harmonic N : ℚ) : ℝ) ≤ 1 + log N := harmonic_le_one_add_log N
  linarith

/-- N has at most log N over log 2 prime factors. -/
theorem bc_card_primeFactors_le (N : ℕ) (hN : 1 ≤ N) :
    (N.primeFactors.card : ℝ) ≤ log N / log 2 := by
  have h2 : 2 ^ N.primeFactors.card ≤ ∏ p ∈ N.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have hle : ∏ p ∈ N.primeFactors, p ≤ N :=
    Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd N)
  have hR : (2 : ℝ) ^ N.primeFactors.card ≤ N := by exact_mod_cast h2.trans hle
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  rw [le_div_iff₀ hl2]
  have := Real.log_le_log (by positivity) hR
  rwa [Real.log_pow] at this

/-- For a positive real x, the naturals n with log n over L equal to x form a set with
at most one element. -/
theorem bc_card_level_le (s : Finset ℕ) (L x : ℝ) (hL : 0 < L) :
    (s.filter (fun n : ℕ => 0 < n ∧ log (n : ℝ) / L = x)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro m hm n hn
  simp only [Finset.mem_filter] at hm hn
  have h : log (m : ℝ) = log (n : ℝ) := by
    have := hm.2.2.trans hn.2.2.symm
    field_simp at this
    linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.2.1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.2.1
  exact_mod_cast Real.log_injOn_pos hm0 hn0 h

/-- A level bound gives a power bound. -/
theorem bc_rpow_le_of_level {N n : ℕ} (hN : 2 ≤ N) (hn : 0 < n) {c : ℝ}
    (h : c ≤ log (n : ℝ) / log N) : (N : ℝ) ^ c ≤ n := by
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ hL] at h
  rw [Real.rpow_def_of_pos hN0]
  calc rexp (log N * c) ≤ rexp (log n) := Real.exp_le_exp.mpr (by linarith)
    _ = n := Real.exp_log hn0

/-- K log N squared over N to c tends to 0 for c positive. -/
theorem bc_decay_tendsto {c : ℝ} (hc : 0 < c) (K : ℝ) :
    Tendsto (fun N : ℕ => K * (log (N : ℝ)) ^ 2 / (N : ℝ) ^ c) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hc).tendsto_div_nhds_zero
  have h' : Tendsto (fun x : ℝ => K * (log x ^ (2 : ℝ) / x ^ c)) atTop (𝓝 0) := by
    simpa using h.const_mul K
  have := h'.comp tendsto_natCast_atTop_atTop
  refine this.congr' (Eventually.of_forall fun N => ?_)
  simp only [Function.comp, Real.rpow_two]
  ring

/-- Primes dividing N or at two levels number at most the prime factor count plus 2. -/
theorem bc_card_bad_le (N : ℕ) (hN : 1 ≤ N) (s : Finset ℕ) (hs : ∀ n ∈ s, n.Prime)
    (L x y : ℝ) (hL : 0 < L) (R : ℕ → Prop) [DecidablePred R]
    (hR : ∀ n ∈ s, R n → (n ∣ N ∨ log (n : ℝ) / L = x ∨ log (n : ℝ) / L = y)) :
    ((s.filter R).card : ℝ) ≤ N.primeFactors.card + 2 := by
  have hsub : s.filter R ⊆ (N.primeFactors ∪ s.filter (fun n : ℕ => 0 < n ∧ log (n : ℝ) / L = x)) ∪
      s.filter (fun n : ℕ => 0 < n ∧ log (n : ℝ) / L = y) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    have hp := hs n hn.1
    rcases hR n hn.1 hn.2 with h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Nat.mem_primeFactors.mpr ⟨hp, h, by omega⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hn.1, hp.pos, h⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn.1, hp.pos, h⟩)
  have h1 := bc_card_level_le s L x hL
  have h2 := bc_card_level_le s L y hL
  have hc := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le (N.primeFactors ∪ s.filter (fun n : ℕ => 0 < n ∧ log (n : ℝ) / L = x))
    (s.filter (fun n : ℕ => 0 < n ∧ log (n : ℝ) / L = y))
  have hu2 := Finset.card_union_le N.primeFactors (s.filter (fun n : ℕ => 0 < n ∧ log (n : ℝ) / L = x))
  have : (s.filter R).card ≤ N.primeFactors.card + 2 := by omega
  exact_mod_cast this


/-- Wu 2004 page 41: the switched pairs are the free pairs coprime to N. -/
theorem bc_switched_subset (N : ℕ) (i : Fin 12) : switchedPairs N i ⊆ freePairs N i := by
  intro x hx
  simp only [switchedPairs, Wu08Sum.P2, freePairs, Finset.mem_filter] at hx ⊢
  tauto

/-- Wu 2004 page 41: for a free pair, p q cubed is below N squared, so log N is at most
3 times log of N over p q. -/
theorem bc_log_ratio {N : ℕ} (hN : 2 ≤ N) {i : Fin 12} {x : ℕ × ℕ} (hx : x ∈ freePairs N i) :
    0 < log ((N : ℝ) / ((x.1 : ℝ) * x.2)) ∧
      log (N : ℝ) ≤ 3 * log ((N : ℝ) / ((x.1 : ℝ) * x.2)) := by
  simp only [freePairs, Finset.mem_filter] at hx
  obtain ⟨_, hp, hq, _, hpq, hqs⟩ := hx
  have hp0 : (0 : ℝ) < x.1 := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < x.2 := by exact_mod_cast hq.pos
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hpqr : (x.1 : ℝ) < x.2 := by exact_mod_cast hpq
  have hsq : (x.2 : ℝ) ^ 2 < N / x.1 := by
    have h0 : 0 ≤ (x.2 : ℝ) := hq0.le
    calc (x.2 : ℝ) ^ 2 < sqrt ((N : ℝ) / (x.1 : ℝ)) ^ 2 := by
          exact pow_lt_pow_left₀ hqs h0 (by norm_num)
      _ = (N : ℝ) / (x.1 : ℝ) := Real.sq_sqrt (by positivity)
  have h1 : (x.1 : ℝ) * x.2 ^ 2 < N := by
    rwa [lt_div_iff₀ hp0, mul_comm] at hsq
  have hcube : ((x.1 : ℝ) * x.2) ^ 3 < (N : ℝ) ^ 2 := by
    have h2 : ((x.1 : ℝ) * x.2) ^ 3 ≤ ((x.1 : ℝ) * x.2 ^ 2) ^ 2 := by
      have : ((x.1 : ℝ) * x.2 ^ 2) ^ 2 - ((x.1 : ℝ) * x.2) ^ 3 =
          (x.1 : ℝ) ^ 2 * x.2 ^ 3 * (x.2 - x.1) := by ring
      nlinarith [mul_pos (mul_pos (pow_pos hp0 2) (pow_pos hq0 3)) (sub_pos.mpr hpqr)]
    have h3 : ((x.1 : ℝ) * x.2 ^ 2) ^ 2 < (N : ℝ) ^ 2 :=
      pow_lt_pow_left₀ h1 (by positivity) (by norm_num)
    linarith
  have hpq0 : (0 : ℝ) < (x.1 : ℝ) * x.2 := mul_pos hp0 hq0
  have hlog : 3 * log ((x.1 : ℝ) * x.2) < 2 * log (N : ℝ) := by
    have := Real.log_lt_log (by positivity) hcube
    rwa [Real.log_pow, Real.log_pow] at this
  have hlt : (x.1 : ℝ) * x.2 < N := by
    by_contra hcon
    push Not at hcon
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have h3 : (N : ℝ) ^ 3 ≤ ((x.1 : ℝ) * x.2) ^ 3 := pow_le_pow_left₀ hN0.le hcon 3
    have h4 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 := pow_le_pow_right₀ hN1 (by norm_num)
    linarith
  rw [Real.log_div hN0.ne' hpq0.ne']
  have hLN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (by omega : 1 < N))
  constructor <;> nlinarith [Real.log_lt_log hpq0 hlt]

/-- Wu 2004 page 41: both primes of a free pair are at least N to kappa2. -/
theorem bc_free_lower {N : ℕ} (hN : 2 ≤ N) {i : Fin 12} {x : ℕ × ℕ} (hx : x ∈ freePairs N i) :
    (N : ℝ) ^ kappa2 ≤ x.1 ∧ (N : ℝ) ^ kappa2 ≤ x.2 := by
  simp only [freePairs, Finset.mem_filter] at hx
  obtain ⟨_, _, _, hc, hpq, _⟩ := hx
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have h1 : (N : ℝ) ^ kappa2 ≤ x.1 := by
    split_ifs at hc
    · exact (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num [kappa2, sigma1])).trans hc
    · exact (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num [kappa2, sigma2])).trans hc
    · exact hc.1
  refine ⟨h1, h1.trans ?_⟩
  exact_mod_cast hpq.le

/-- `leaf_coprime_removal`, exactly as stated in Decomp349bSplitSum, Wu 2004 page 41:
the pairs with a prime dividing N contribute o of 1 over log N. Proved. -/
theorem leaf_coprime_removal_proved :
    ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
      Tendsto (fun N : ℕ => 8 * log N * (switchedSum N i - freeSum N i)) evenAtTop
        (𝓝 0) := by
  intro i _
  have hc : (0 : ℝ) < kappa2 := by norm_num [kappa2]
  have hl2 : 0 < log 2 := log_pos (by norm_num)
  refine Tendsto.mono_left ?_ (inf_le_left : evenAtTop ≤ atTop)
  refine squeeze_zero_norm' ?_ (bc_decay_tendsto hc (192 * (1 / log 2 + 2)))
  filter_upwards [eventually_ge_atTop 3] with N hN3
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hN0 : (0 : ℝ) < N := by linarith
  have hL : 0 < log (N : ℝ) := log_pos (by linarith)
  have hL1 : 1 ≤ log (N : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  set w : ℕ × ℕ → ℝ := fun x => 1 / (((x.1 : ℝ) * x.2) * log ((N : ℝ) / ((x.1 : ℝ) * x.2)))
    with hw
  set f : ℕ × ℕ → ℝ := fun x => 1 / ((x.1 : ℝ) * x.2) with hf
  set Bd := freePairs N i \ switchedPairs N i with hBd
  have hdiff : freeSum N i - switchedSum N i = ∑ x ∈ Bd, w x := by
    have h := Finset.sum_sdiff (f := w) (bc_switched_subset N i)
    simp only [freeSum, switchedSum]
    linarith
  have hwnn : ∀ x ∈ freePairs N i, 0 ≤ w x := by
    intro x hx
    have h := (bc_log_ratio (by omega) hx).1
    have hp := (Finset.mem_filter.mp hx).2.1
    have hq := (Finset.mem_filter.mp hx).2.2.1
    have hp0 : (0 : ℝ) < x.1 := by exact_mod_cast hp.pos
    have hq0 : (0 : ℝ) < x.2 := by exact_mod_cast hq.pos
    simp only [hw]; positivity
  have hwf : ∀ x ∈ freePairs N i, log (N : ℝ) * w x ≤ 3 * f x := by
    intro x hx
    obtain ⟨h0, h3⟩ := bc_log_ratio (by omega) hx
    have hp := (Finset.mem_filter.mp hx).2.1
    have hq := (Finset.mem_filter.mp hx).2.2.1
    have hp0 : (0 : ℝ) < x.1 := by exact_mod_cast hp.pos
    have hq0 : (0 : ℝ) < x.2 := by exact_mod_cast hq.pos
    have hpq0 : (0 : ℝ) < (x.1 : ℝ) * x.2 := mul_pos hp0 hq0
    simp only [hw, hf]
    have he : log (N : ℝ) * (1 / ((x.1 : ℝ) * x.2 * log ((N : ℝ) / ((x.1 : ℝ) * x.2)))) =
        (log (N : ℝ) / log ((N : ℝ) / ((x.1 : ℝ) * x.2))) * (1 / ((x.1 : ℝ) * x.2)) := by
      field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_right ((div_le_iff₀ h0).mpr (by linarith)) (by positivity)
  set Q := (Finset.range (N + 1)).filter Nat.Prime with hQ
  set Pd := Q.filter (fun p : ℕ => (N : ℝ) ^ kappa2 ≤ (p : ℝ) ∧ (p ∣ N ∨ False ∨ False))
    with hPd
  have hsub : Bd ⊆ (Pd ×ˢ Q) ∪ (Q ×ˢ Pd) := by
    intro x hx
    rw [hBd, Finset.mem_sdiff] at hx
    have hlow := bc_free_lower (by omega) hx.1
    have hmem := Finset.mem_filter.mp hx.1
    have hr := Finset.mem_product.mp hmem.1
    have hp := hmem.2.1
    have hq := hmem.2.2.1
    have hpQ : x.1 ∈ Q := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (by have := Finset.mem_range.mp hr.1; omega), hp⟩
    have hqQ : x.2 ∈ Q := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (by have := Finset.mem_range.mp hr.2; omega), hq⟩
    have hnc : x.1 ∣ N ∨ x.2 ∣ N := by
      by_contra hcon
      push Not at hcon
      apply hx.2
      simp only [switchedPairs, Wu08Sum.P2, Finset.mem_filter]
      exact ⟨hmem.1, hp, hq, (Nat.Prime.coprime_iff_not_dvd hp).mpr hcon.1,
        (Nat.Prime.coprime_iff_not_dvd hq).mpr hcon.2, hmem.2.2.2⟩
    rcases hnc with h | h
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨hpQ, hlow.1, Or.inl h⟩, hqQ⟩)
    · exact Finset.mem_union_right _ (Finset.mem_product.mpr
        ⟨hpQ, Finset.mem_filter.mpr ⟨hqQ, hlow.2, Or.inl h⟩⟩)
  have hQprime : ∀ n ∈ Q, n.Prime := fun n hn => (Finset.mem_filter.mp hn).2
  have hH := bc_prime_recip_le N
  have hpf := bc_card_primeFactors_le N (by omega)
  set cp : ℝ := (N.primeFactors.card : ℝ) + 2 with hcp
  have hNc : 0 < (N : ℝ) ^ kappa2 := Real.rpow_pos_of_pos hN0 _
  have hfnn : ∀ x, 0 ≤ f x := fun x => by simp only [hf]; positivity
  have hsumPd : ∑ p ∈ Pd, (1 / (p : ℝ)) ≤ cp / (N : ℝ) ^ kappa2 := by
    have hcard : (Pd.card : ℝ) ≤ cp :=
      bc_card_bad_le N (by omega) Q hQprime (log N) 0 0 hL _ (fun n _ h => by
        rcases h.2 with h | h | h
        · exact Or.inl h
        · exact h.elim
        · exact h.elim)
    have hterm : ∀ p ∈ Pd, (1 / (p : ℝ)) ≤ 1 / (N : ℝ) ^ kappa2 := fun p hp =>
      one_div_le_one_div_of_le hNc (Finset.mem_filter.mp hp).2.1
    calc ∑ p ∈ Pd, (1 / (p : ℝ)) ≤ Pd.card • (1 / (N : ℝ) ^ kappa2) :=
          Finset.sum_le_card_nsmul _ _ _ hterm
      _ = (Pd.card : ℝ) * (1 / (N : ℝ) ^ kappa2) := by rw [nsmul_eq_mul]
      _ ≤ cp * (1 / (N : ℝ) ^ kappa2) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = cp / (N : ℝ) ^ kappa2 := by ring
  have hS0 : 0 ≤ ∑ q ∈ Q, (1 : ℝ) / q := Finset.sum_nonneg fun _ _ => by positivity
  have hP1 : ∑ x ∈ Pd ×ˢ Q, f x ≤ cp / (N : ℝ) ^ kappa2 * (1 + log N) := by
    rw [Finset.sum_product]
    simp only [hf, ← one_div_mul_one_div, ← Finset.mul_sum, ← Finset.sum_mul]
    calc (∑ p ∈ Pd, 1 / (p : ℝ)) * ∑ q ∈ Q, (1 : ℝ) / q
        ≤ cp / (N : ℝ) ^ kappa2 * ∑ q ∈ Q, (1 : ℝ) / q := mul_le_mul_of_nonneg_right hsumPd hS0
      _ ≤ _ := mul_le_mul_of_nonneg_left hH (by positivity)
  have hP2 : ∑ x ∈ Q ×ˢ Pd, f x ≤ cp / (N : ℝ) ^ kappa2 * (1 + log N) := by
    rw [Finset.sum_product]
    simp only [hf, ← one_div_mul_one_div, ← Finset.mul_sum, ← Finset.sum_mul]
    calc (∑ p ∈ Q, 1 / (p : ℝ)) * ∑ q ∈ Pd, (1 : ℝ) / q
        ≤ (1 + log N) * ∑ q ∈ Pd, (1 : ℝ) / q :=
          mul_le_mul_of_nonneg_right hH (Finset.sum_nonneg fun _ _ => by positivity)
      _ ≤ (1 + log N) * (cp / (N : ℝ) ^ kappa2) :=
          mul_le_mul_of_nonneg_left hsumPd (by positivity)
      _ = _ := by ring
  have hU : ∑ x ∈ (Pd ×ˢ Q) ∪ (Q ×ˢ Pd), f x ≤ ∑ x ∈ Pd ×ˢ Q, f x + ∑ x ∈ Q ×ˢ Pd, f x := by
    rw [← Finset.sum_union_inter]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun x _ => hfnn x)
  have hBdf : log (N : ℝ) * ∑ x ∈ Bd, w x ≤ 3 * ∑ x ∈ Bd, f x := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun x hx => hwf x (Finset.mem_sdiff.mp hx).1
  have hBdsub : ∑ x ∈ Bd, f x ≤ ∑ x ∈ (Pd ×ˢ Q) ∪ (Q ×ˢ Pd), f x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hfnn x)
  have hBw0 : 0 ≤ ∑ x ∈ Bd, w x :=
    Finset.sum_nonneg fun x hx => hwnn x (Finset.mem_sdiff.mp hx).1
  have hcpL : cp ≤ (1 / log 2 + 2) * log N := by
    have : log (N : ℝ) / log 2 = (1 / log 2) * log N := by ring
    rw [hcp]; nlinarith
  have hfin : 24 * (cp / (N : ℝ) ^ kappa2 * (1 + log N)) ≤
      96 * (1 / log 2 + 2) * log (N : ℝ) ^ 2 / (N : ℝ) ^ kappa2 := by
    rw [div_mul_eq_mul_div, mul_div_assoc', div_le_div_iff_of_pos_right hNc]
    have h12 : 0 ≤ 1 / log 2 + 2 := by positivity
    nlinarith
  rw [Real.norm_eq_abs, show switchedSum N i - freeSum N i = -(freeSum N i - switchedSum N i)
    by ring, hdiff, mul_neg, abs_neg, abs_of_nonneg (by positivity)]
  calc 8 * log (N : ℝ) * ∑ x ∈ Bd, w x = 8 * (log (N : ℝ) * ∑ x ∈ Bd, w x) := by ring
    _ ≤ 8 * (3 * (cp / (N : ℝ) ^ kappa2 * (1 + log N) + cp / (N : ℝ) ^ kappa2 * (1 + log N))) := by
        nlinarith
    _ = 24 * (cp / (N : ℝ) ^ kappa2 * (1 + log N)) * 2 := by ring
    _ ≤ 96 * (1 / log 2 + 2) * log (N : ℝ) ^ 2 / (N : ℝ) ^ kappa2 * 2 := by nlinarith
    _ = _ := by ring
end LeanLab.ChenDoubleSieve.Task349

