/-
Cai 2002 page 604 display 4.15. Supply split for the all large pair region.
The mixed pair Huxley limit is not substituted into this distinct region.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Decomp337b

open Filter Finset Real
open scoped Topology
noncomputable section
namespace LeanLab.Cai2002

/-- Every all large triple counted by rho3 has a prime value in the closed switched index.
Page 604 display 4.15, using the finite switching step of page 602 display 4.8. -/
theorem rho3_closed_fiber337 (N p : ℕ) (hN : 2 ≤ N) (hp : p ∈ Pset N 0.95) :
    rho3 (z2 N) (N - p) ≤
      (((switchedClosedIndex337 N (switchedThreeE306 N)).filter
        (fun b => (N - b.1 * b.2).Prime)).filter
          (fun b => N - b.1 * b.2 = p)).card := by
  classical
  unfold rho3
  split_ifs with hw
  · obtain ⟨x, y, r, hx, hy, hr, hprod, hx2, hxy, hyr⟩ := hw
    obtain ⟨hroot, hcop, hdata⟩ := triple_switch_data337 N p x y r hp hx hy hr hyr hprod
    have hpair : (x, y) ∈ switchedThreePairs306 N :=
      (mem_switchedThreePairs306 N x y hN).mpr ⟨hx, hy, hx2, hxy, hroot, hcop⟩
    have hE : x * y ∈ switchedThreeE306 N := mem_image.mpr ⟨(x, y), hpair, rfl⟩
    obtain ⟨hb, hback⟩ := hdata _ hE
    apply Finset.card_pos.mpr
    refine ⟨(x * y, r), mem_filter.mpr ⟨mem_filter.mpr ⟨hb, ?_⟩, hback⟩⟩
    simpa only [hback] using (mem_Pset hp).2.1
  · exact Nat.zero_le _

/-- S3 is bounded by the prime values of the closed all large switched sequence.
Page 604 display 4.15. Every fibre retains the full indexed multiplicity. -/
theorem sieve_three_closed337 (N : ℕ) (hN : 2 ≤ N) :
    S3 N 0.95 ≤ ((switchedClosedIndex337 N (switchedThreeE306 N)).filter
      (fun b => (N - b.1 * b.2).Prime)).card := by
  classical
  unfold S3
  calc
    _ ≤ ∑ p ∈ Pset N 0.95,
        (((switchedClosedIndex337 N (switchedThreeE306 N)).filter
          (fun b => (N - b.1 * b.2).Prime)).filter
            (fun b => N - b.1 * b.2 = p)).card :=
      sum_le_sum (fun p hp => rho3_closed_fiber337 N p hN hp)
    _ = _ := sum_card_fiberwise_eq_card_filter _ _ _
    _ ≤ _ := card_filter_le _ _

#print axioms rho3_closed_fiber337
#print axioms sieve_three_closed337

/-- The complete finite S3 bridge retains the small prime and closed endpoint losses.
Page 604 display 4.15 by the finite argument in page 602 displays 4.8 to 4.9.
This is unconditional and does not use the mixed Huxley limit. -/
theorem sieve_three_switching_finite337 (N : ℕ) (hN : 2 ≤ N)
    (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℝ) :
    let PP : ℕ := ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p
    S3 N 0.95 ≤ ((switchedIndex306 N (switchedThreeE306 N)).filter
      (fun b => (N - b.1 * b.2).Coprime PP)).card +
        (switchedThreeE306 N).card * (⌈z⌉₊ + 1) := by
  dsimp only
  have h0 := sieve_three_closed337 N hN
  have h1 := switched_closed_selection337 N hN (switchedThreeE306 N) Nat.Prime
  have h2 := switched_prime_sift337 N hN (switchedThreeE306 N) P hP z
  dsimp only at h2
  have h := h0.trans (h1.trans (Nat.add_le_add_right h2 _))
  simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using h

#print axioms sieve_three_switching_finite337

/-- Each all large product is positive and below N to two thirds.
Page 604 display 4.15, using the analogous E range of page 602. -/
theorem switchedThreeE_range337 (N e : ℕ) (hN : 2 ≤ N) (he : e ∈ switchedThreeE306 N) :
    0 < e ∧ (e : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ) := by
  obtain ⟨b, hb, rfl⟩ := mem_image.mp he
  obtain ⟨hp, hq, _, hpq, hroot, _⟩ :=
    (mem_switchedThreePairs306 N b.1 b.2 hN).mp hb
  have hp0 : (0 : ℝ) < b.1 := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < b.2 := by exact_mod_cast hq.pos
  have hpqR : (b.1 : ℝ) < b.2 := by exact_mod_cast hpq
  rw [← sqrt_eq_rpow, lt_sqrt hq0.le] at hroot
  have hsmall : (b.1 : ℝ) * (b.2 : ℝ) ^ 2 < N := by
    have hh := (lt_div_iff₀ hp0).mp hroot
    nlinarith only [hh]
  have hlt : (b.1 : ℝ) ^ 2 * b.2 < (b.1 : ℝ) * (b.2 : ℝ) ^ 2 := by
    nlinarith [mul_pos (mul_pos hp0 hq0) (sub_pos.mpr hpqR)]
  have hcube : ((b.1 : ℝ) * b.2) ^ 3 < (N : ℝ) ^ 2 := by
    calc
      _ = ((b.1 : ℝ) * (b.2 : ℝ) ^ 2) * ((b.1 : ℝ) ^ 2 * b.2) := by ring
      _ < ((b.1 : ℝ) * (b.2 : ℝ) ^ 2) ^ 2 := by
        nlinarith [mul_pos (mul_pos hp0 (sq_pos_of_pos hq0)) (sub_pos.mpr hlt)]
      _ < _ := pow_lt_pow_left₀ hsmall (by positivity) (by norm_num)
  have hpow : ((N : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (N : ℝ) ^ 2 := by
    rw [← rpow_natCast, ← rpow_mul (Nat.cast_nonneg N)]
    norm_num
  have hh : (b.1 : ℝ) * b.2 < (N : ℝ) ^ (2 / 3 : ℝ) :=
    lt_of_pow_lt_pow_left₀ 3 (rpow_nonneg (Nat.cast_nonneg N) _) (by rwa [hpow])
  exact ⟨Nat.mul_pos hp.pos hq.pos, by exact_mod_cast hh⟩

/-- The all large product support has at most ceil N to two thirds elements.
Page 604 display 4.15, using the analogous E range of page 602. -/
theorem switchedThreeE_card337 (N : ℕ) (hN : 2 ≤ N) :
    (switchedThreeE306 N).card ≤ ⌈(N : ℝ) ^ (2 / 3 : ℝ)⌉₊ := by
  have hsub : switchedThreeE306 N ⊆ range ⌈(N : ℝ) ^ (2 / 3 : ℝ)⌉₊ := by
    intro e he
    exact mem_range.mpr (Nat.lt_ceil.mpr (switchedThreeE_range337 N e hN he).2)
  simpa only [card_range] using card_le_card hsub

#print axioms switchedThreeE_card337

/-- Every prime factor of an all large product is at least z1.
Page 604 display 4.15 by the support argument for display 4.11 on page 603. -/
theorem switchedThreeE_rough337 (N e : ℕ) (hN : 2 ≤ N) (he : e ∈ switchedThreeE306 N) :
    ∀ p ∈ e.primeFactors, z1 N ≤ (p : ℝ) := by
  obtain ⟨b, hb, rfl⟩ := mem_image.mp he
  obtain ⟨hx, hy, hx2, hxy, _, _⟩ :=
    (mem_switchedThreePairs306 N b.1 b.2 hN).mp hb
  have hz : z1 N ≤ z2 N := rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  rcases hprime.dvd_mul.mp (Nat.dvd_of_mem_primeFactors hp) with hpx | hpy
  · have heq := (Nat.prime_dvd_prime_iff_eq hprime hx).mp hpx
    simpa only [heq] using hz.trans hx2
  · have heq := (Nat.prime_dvd_prime_iff_eq hprime hy).mp hpy
    have hxyR : (b.1 : ℝ) ≤ b.2 := by exact_mod_cast hxy.le
    simpa only [heq] using hz.trans (hx2.trans hxyR)

/-- The actual all large product region has a negligible omitted Li remainder.
Page 604 display 4.15, using the proved noncoprime estimate of page 603 display 4.11.
The mixed Huxley limit is not used. -/
theorem sieve_three_R2_small337 (η : ℝ) (hη : 0 < η) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ D : ℕ, D ≤ N →
      (∑ d ∈ Icc 1 D,
        |∑ e ∈ (switchedThreeE306 N).filter (fun e => ¬ e.Coprime d),
          switchedLiTerm337 N e / (d.totient : ℝ)|) ≤
          η * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
  obtain ⟨n0, hn0⟩ := switched_li_remainder_small337 η hη
  refine ⟨max 2 n0, fun N hN D hD => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left ..).trans hN
  apply hn0 N ((le_max_right ..).trans hN) (switchedThreeE306 N) _ D hD
  intro e he
  have hh := switchedThreeE_range337 N e hN2 he
  exact ⟨hh.1, hh.2.le, switchedThreeE_rough337 N e hN2 he⟩

#print axioms switchedThreeE_range337
#print axioms switchedThreeE_rough337
#print axioms sieve_three_R2_small337

/-- The positive product support satisfies the paper's strict real cardinality bound.
Page 604 display 4.15, the strict analogue of the E size bound on page 602. -/
theorem switchedThreeE_card_lt337 (N : ℕ) (hN : 2 ≤ N) :
    (switchedThreeE306 N).card < (N : ℝ) ^ (2 / 3 : ℝ) := by
  let R : ℝ := (N : ℝ) ^ (2 / 3 : ℝ)
  have hRp : 0 < R := rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hceil : 1 ≤ ⌈R⌉₊ := Nat.one_le_ceil_iff.mpr hRp
  have hsub : switchedThreeE306 N ⊆ Icc 1 (⌈R⌉₊ - 1) := by
    intro e he
    have hh := switchedThreeE_range337 N e hN he
    have hc : e < ⌈R⌉₊ := Nat.lt_ceil.mpr hh.2
    exact mem_Icc.mpr ⟨hh.1, by omega⟩
  have hcard : (switchedThreeE306 N).card ≤ ⌈R⌉₊ - 1 := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hsub
  have hc : ((switchedThreeE306 N).card : ℝ) ≤ (⌈R⌉₊ - 1 : ℕ) := by exact_mod_cast hcard
  have hlt : ((⌈R⌉₊ - 1 : ℕ) : ℝ) < R := by
    rw [Nat.cast_sub hceil, Nat.cast_one]
    linarith [Nat.ceil_lt_add_one hRp.le]
  exact hc.trans_lt hlt

#print axioms switchedThreeE_card_lt337

/-- The normalized all large prime pair sum in the first line of display 4.15.
The ordering keeps the unique prime pair enumeration from Decomp306d. -/
def sieveThreePairSum337 (N : ℕ) : ℝ :=
  8 / (2 * (0.95 : ℝ) - 1) * log N *
    ∑ b ∈ switchedThreePairs306 N,
      1 / ((b.1 * b.2 : ℕ) * log ((N : ℝ) / (b.1 * b.2 : ℕ)))

/-- The exact integral coefficient in the second line of display 4.15. -/
def sieveThreeCoefficient337 : ℝ :=
  8 / (2 * (0.95 : ℝ) - 1) * ∫ t in (2 : ℝ)..2.29, log (t - 1) / t

private theorem bsc3_blk_sum (L : ℝ) (hL : 0 < L) (t : ℕ → ℝ) (ht : Monotone t) (h2 : log 2 ≤ t 0 * L)
    (f : ℝ → ℝ) (M : ℕ → ℝ) (K : ℕ)
    (hM : ∀ j < K, ∀ v, t j < v → v ≤ t (j+1) → f v ≤ M j) (hM0 : ∀ j < K, 0 ≤ M j) :
    ∑ q ∈ Ioc ⌊exp (t 0 * L)⌋₊ ⌊exp (t K * L)⌋₊, (if q.Prime then f (log q / L) / q else 0) ≤
      ∑ j ∈ range K, M j * (log (t (j+1) / t j) + 4 / (t j * L)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ]
    have hmon : ∀ a b : ℕ, a ≤ b → ⌊exp (t a * L)⌋₊ ≤ ⌊exp (t b * L)⌋₊ := fun a b hab =>
      Nat.floor_le_floor (exp_le_exp.mpr (mul_le_mul_of_nonneg_right (ht hab) hL.le))
    rw [← sum_Ioc_consecutive _ (hmon 0 K (Nat.zero_le _)) (hmon K (K+1) (Nat.le_succ _))]
    have ih' := ih (fun j hj v h1 h3 => hM j (by omega) v h1 h3) (fun j hj => hM0 j (by omega))
    have hy2 : (2 : ℝ) ≤ exp (t K * L) := by
      have : log 2 ≤ t K * L := h2.trans (mul_le_mul_of_nonneg_right (ht (Nat.zero_le _)) hL.le)
      calc (2:ℝ) = exp (log 2) := (exp_log (by norm_num)).symm
        _ ≤ _ := exp_le_exp.mpr this
    have hyx : exp (t K * L) ≤ exp (t (K+1) * L) :=
      exp_le_exp.mpr (mul_le_mul_of_nonneg_right (ht (Nat.le_succ _)) hL.le)
    have hmert := LeanLab.AlmostPrimes.Decomp1528b.mertens2_block hy2 hyx
    have hupper := (abs_le.mp hmert).2
    have htK : 0 < t K * L := lt_of_lt_of_le (log_pos (by norm_num)) (h2.trans
      (mul_le_mul_of_nonneg_right (ht (Nat.zero_le _)) hL.le))
    have htK0 : 0 < t K := pos_of_mul_pos_left htK hL.le
    have htK1 : 0 < t (K+1) := lt_of_lt_of_le htK0 (ht (Nat.le_succ _))
    have hll : log (log (exp (t (K+1) * L))) - log (log (exp (t K * L))) = log (t (K+1) / t K) := by
      rw [log_exp, log_exp, log_mul htK1.ne' hL.ne', log_mul htK0.ne' hL.ne', log_div htK1.ne' htK0.ne']
      ring
    rw [hll, log_exp] at hupper
    have hblock : ∑ q ∈ Ioc ⌊exp (t K * L)⌋₊ ⌊exp (t (K+1) * L)⌋₊,
        (if q.Prime then f (log q / L) / q else 0) ≤
        M K * ∑ p ∈ (Ioc ⌊exp (t K * L)⌋₊ ⌊exp (t (K+1) * L)⌋₊).filter Nat.Prime, (1 : ℝ) / p := by
      rw [sum_filter, mul_sum]
      apply sum_le_sum
      intro q hq
      split_ifs with hp
      · have hq1 := (mem_Ioc.mp hq).1
        have hq2 := (mem_Ioc.mp hq).2
        have hy : exp (t K * L) < q := (Nat.floor_lt (exp_pos _).le).mp hq1
        have hx : (q : ℝ) ≤ exp (t (K+1) * L) := (Nat.le_floor_iff (exp_pos _).le).mp hq2
        have hqpos : (0 : ℝ) < q := lt_trans (exp_pos _) hy
        have hv1 : t K < log q / L := by
          rw [lt_div_iff₀ hL]
          have := log_lt_log (exp_pos _) hy
          rwa [log_exp] at this
        have hv2 : log q / L ≤ t (K+1) := by
          rw [div_le_iff₀ hL]
          have := log_le_log hqpos hx
          rwa [log_exp] at this
        have hfv := hM K (Nat.lt_succ_self K) _ hv1 hv2
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right hfv hqpos.le
      · simp
    have hM0K := hM0 K (Nat.lt_succ_self K)
    have := mul_le_mul_of_nonneg_left hupper hM0K
    linarith

private theorem bsc3_riem (t : ℕ → ℝ) (K : ℕ) (Δ : ℝ) (f : ℝ → ℝ) (m : ℕ → ℝ)
    (ht : ∀ j < K, t j ≤ t (j+1)) (ht0 : ∀ j < K, 0 < t j)
    (hΔ : ∀ j < K, log (t (j+1) / t j) = Δ)
    (hm : ∀ j < K, ∀ u ∈ Set.Icc (t j) (t (j+1)), m j ≤ f u)
    (hint : ∀ j < K, IntervalIntegrable (fun u => f u / u) MeasureTheory.volume (t j) (t (j+1))) :
    ∑ j ∈ range K, m j * Δ ≤ ∫ u in (t 0)..(t K), f u / u := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals hint]
  apply sum_le_sum
  intro j hj
  have hj' := mem_range.mp hj
  have h0 := ht0 j hj'
  have h1 : 0 < t (j+1) := lt_of_lt_of_le h0 (ht j hj')
  have heq : m j * Δ = ∫ u in (t j)..(t (j+1)), m j / u := by
    simp only [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos h0 h1, hΔ j hj']
  rw [heq]
  apply intervalIntegral.integral_mono_on (ht j hj')
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro u hu
    rw [Set.uIcc_of_le (ht j hj')] at hu
    exact (lt_of_lt_of_le h0 hu.1).ne'
  · exact hint j hj'
  · intro u hu
    exact div_le_div_of_nonneg_right (hm j hj' u hu) (lt_of_lt_of_le h0 hu.1).le

private theorem bsc3_geo_part (α β : ℝ) (K : ℕ) (hK : 0 < K) (hα : 0 < α) (hαβ : α ≤ β) :
    let Δ := log (β / α) / K
    let t : ℕ → ℝ := fun j => α * exp (j * Δ)
    0 ≤ Δ ∧ Monotone t ∧ t 0 = α ∧ t K = β ∧ (∀ j, log (t (j+1) / t j) = Δ) := by
  intro Δ t
  have hΔ0 : 0 ≤ Δ := div_nonneg (log_nonneg ((one_le_div hα).mpr hαβ)) (Nat.cast_nonneg _)
  refine ⟨hΔ0, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    apply mul_le_mul_of_nonneg_left _ hα.le
    apply exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hΔ0
  · simp [t]
  · simp only [t, Δ]
    rw [mul_div_cancel₀ _ (by exact_mod_cast hK.ne' : (K:ℝ) ≠ 0), exp_log (div_pos (by linarith) hα)]
    field_simp
  · intro j
    simp only [t]
    rw [mul_div_mul_left _ _ hα.ne', ← exp_sub, log_exp]
    push_cast; ring

private theorem bsc3_fint (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) (f : ℝ → ℝ)
    (h1 : IntervalIntegrable f MeasureTheory.volume α β) :
    IntervalIntegrable (fun u => f u / u) MeasureTheory.volume α β := by
  simp only [div_eq_mul_inv]
  apply h1.mul_continuousOn
  apply ContinuousOn.inv₀ continuousOn_id
  intro u hu; rw [Set.uIcc_of_le hαβ] at hu; exact (lt_of_lt_of_le hα hu.1).ne'

private theorem bsc3_mono_sum (L α β : ℝ) (K : ℕ) (hK : 0 < K) (hL : 0 < L) (hα : 0 < α) (hαβ : α ≤ β)
    (h2 : log 2 ≤ α * L) (f : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc α β))
    (hf0 : ∀ v ∈ Set.Icc α β, 0 ≤ f v) :
    ∑ q ∈ Ioc ⌊exp (α * L)⌋₊ ⌊exp (β * L)⌋₊, (if q.Prime then f (log q / L) / q else 0) ≤
      (∫ u in α..β, f u / u) + (f β - f α) * (log (β / α) / K) + K * f β * (4 / (α * L)) := by
  obtain ⟨hΔ0, ht, ht0, htK, hratio⟩ := bsc3_geo_part α β K hK hα hαβ
  set Δ := log (β / α) / K with hΔdef
  set t : ℕ → ℝ := fun j => α * exp (j * Δ) with htdef
  have htα : ∀ j, α ≤ t j := fun j => ht0 ▸ ht (Nat.zero_le j)
  have htβ : ∀ j ≤ K, t j ≤ β := fun j hj => htK ▸ ht hj
  have htpos : ∀ j, 0 < t j := fun j => lt_of_lt_of_le hα (htα j)
  have hb := bsc3_blk_sum L hL t ht (by rw [ht0]; exact h2) f (fun j => f (t (j+1))) K
    (fun j hj v h1 h3 => hf ⟨(htα j).trans h1.le, h3.trans (htβ (j+1) hj)⟩ ⟨htα _, htβ _ hj⟩ h3)
    (fun j hj => hf0 _ ⟨htα _, htβ _ hj⟩)
  rw [ht0, htK] at hb
  beta_reduce at hb
  refine hb.trans ?_
  have hfi : IntervalIntegrable (fun u => f u / u) MeasureTheory.volume α β := by
    apply bsc3_fint α β hα hαβ
    apply MonotoneOn.intervalIntegrable; rwa [Set.uIcc_of_le hαβ]
  have hint : ∀ j < K, IntervalIntegrable (fun u => f u / u) MeasureTheory.volume (t j) (t (j+1)) := by
    intro j hj
    apply hfi.mono_set
    rw [Set.uIcc_of_le hαβ, Set.uIcc_of_le (ht (Nat.le_succ j))]
    exact Set.Icc_subset_Icc (htα j) (htβ _ hj)
  have hr := bsc3_riem t K Δ f (fun j => f (t j)) (fun j _ => ht (Nat.le_succ j)) (fun j _ => htpos j)
    (fun j _ => hratio j)
    (fun j hj u hu => hf ⟨htα _, htβ _ hj.le⟩ ⟨(htα j).trans hu.1, hu.2.trans (htβ _ hj)⟩ hu.1) hint
  rw [ht0, htK] at hr
  beta_reduce at hr
  have htel : ∑ j ∈ range K, (f (t (j+1)) - f (t j)) = f β - f α := by
    rw [sum_range_sub (fun j => f (t j)), htK, ht0]
  have herr : ∑ j ∈ range K, f (t (j+1)) * (4 / (t j * L)) ≤ K * f β * (4 / (α * L)) := by
    have : ∀ j ∈ range K, f (t (j+1)) * (4 / (t j * L)) ≤ f β * (4 / (α * L)) := by
      intro j hj
      have hj' := mem_range.mp hj
      apply mul_le_mul
      · exact hf ⟨htα _, htβ _ hj'⟩ ⟨hαβ, le_rfl⟩ (htβ _ hj')
      · exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hα hL)
          (mul_le_mul_of_nonneg_right (htα j) hL.le)
      · exact (div_pos (by norm_num) (mul_pos (htpos j) hL)).le
      · exact hf0 β ⟨hαβ, le_rfl⟩
    calc _ ≤ ∑ j ∈ range K, f β * (4 / (α * L)) := sum_le_sum this
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  have hsplit : ∑ j ∈ range K, f (t (j+1)) * (log (t (j+1) / t j) + 4 / (t j * L)) =
      ∑ j ∈ range K, f (t j) * Δ + (∑ j ∈ range K, (f (t (j+1)) - f (t j))) * Δ +
      ∑ j ∈ range K, f (t (j+1)) * (4 / (t j * L)) := by
    rw [sum_mul, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl; intro j _; rw [hratio j]; ring
  rw [hsplit, htel]
  linarith

private theorem bsc3_anti_sum (L α β : ℝ) (K : ℕ) (hK : 0 < K) (hL : 0 < L) (hα : 0 < α) (hαβ : α ≤ β)
    (h2 : log 2 ≤ α * L) (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Icc α β))
    (hf0 : ∀ v ∈ Set.Icc α β, 0 ≤ f v) :
    ∑ q ∈ Ioc ⌊exp (α * L)⌋₊ ⌊exp (β * L)⌋₊, (if q.Prime then f (log q / L) / q else 0) ≤
      (∫ u in α..β, f u / u) + (f α - f β) * (log (β / α) / K) + K * f α * (4 / (α * L)) := by
  obtain ⟨hΔ0, ht, ht0, htK, hratio⟩ := bsc3_geo_part α β K hK hα hαβ
  set Δ := log (β / α) / K with hΔdef
  set t : ℕ → ℝ := fun j => α * exp (j * Δ) with htdef
  have htα : ∀ j, α ≤ t j := fun j => ht0 ▸ ht (Nat.zero_le j)
  have htβ : ∀ j ≤ K, t j ≤ β := fun j hj => htK ▸ ht hj
  have htpos : ∀ j, 0 < t j := fun j => lt_of_lt_of_le hα (htα j)
  have hb := bsc3_blk_sum L hL t ht (by rw [ht0]; exact h2) f (fun j => f (t j)) K
    (fun j hj v h1 h3 => hf ⟨htα _, htβ _ hj.le⟩ ⟨(htα j).trans h1.le, h3.trans (htβ (j+1) hj)⟩ h1.le)
    (fun j hj => hf0 _ ⟨htα _, htβ _ hj.le⟩)
  rw [ht0, htK] at hb
  beta_reduce at hb
  refine hb.trans ?_
  have hfi : IntervalIntegrable (fun u => f u / u) MeasureTheory.volume α β := by
    apply bsc3_fint α β hα hαβ
    apply AntitoneOn.intervalIntegrable; rwa [Set.uIcc_of_le hαβ]
  have hint : ∀ j < K, IntervalIntegrable (fun u => f u / u) MeasureTheory.volume (t j) (t (j+1)) := by
    intro j hj
    apply hfi.mono_set
    rw [Set.uIcc_of_le hαβ, Set.uIcc_of_le (ht (Nat.le_succ j))]
    exact Set.Icc_subset_Icc (htα j) (htβ _ hj)
  have hr := bsc3_riem t K Δ f (fun j => f (t (j+1))) (fun j _ => ht (Nat.le_succ j)) (fun j _ => htpos j)
    (fun j _ => hratio j)
    (fun j hj u hu => hf ⟨(htα j).trans hu.1, hu.2.trans (htβ _ hj)⟩ ⟨htα _, htβ _ hj⟩ hu.2) hint
  rw [ht0, htK] at hr
  beta_reduce at hr
  have htel : ∑ j ∈ range K, (f (t j) - f (t (j+1))) = f α - f β := by
    have := sum_range_sub (fun j => f (t j)) K
    rw [htK, ht0] at this
    rw [← neg_sub (f β), ← this, ← sum_neg_distrib]
    apply sum_congr rfl; intro j _; ring
  have herr : ∑ j ∈ range K, f (t j) * (4 / (t j * L)) ≤ K * f α * (4 / (α * L)) := by
    have : ∀ j ∈ range K, f (t j) * (4 / (t j * L)) ≤ f α * (4 / (α * L)) := by
      intro j hj
      have hj' := mem_range.mp hj
      apply mul_le_mul
      · exact hf ⟨le_rfl, hαβ⟩ ⟨htα _, htβ _ hj'.le⟩ (htα j)
      · exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hα hL)
          (mul_le_mul_of_nonneg_right (htα j) hL.le)
      · exact (div_pos (by norm_num) (mul_pos (htpos j) hL)).le
      · exact hf0 α ⟨le_rfl, hαβ⟩
    calc _ ≤ ∑ j ∈ range K, f α * (4 / (α * L)) := sum_le_sum this
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  have hsplit : ∑ j ∈ range K, f (t j) * (log (t (j+1) / t j) + 4 / (t j * L)) =
      ∑ j ∈ range K, f (t (j+1)) * Δ + (∑ j ∈ range K, (f (t j) - f (t (j+1)))) * Δ +
      ∑ j ∈ range K, f (t j) * (4 / (t j * L)) := by
    rw [sum_mul, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl; intro j _; rw [hratio j]; ring
  rw [hsplit, htel]
  linarith

private theorem bsc3_bdry (S : Finset ℕ) (y x B : ℝ) (g : ℕ → ℝ) (hy : 0 ≤ y) (hB : 0 ≤ B)
    (hS : ∀ q ∈ S, q.Prime ∧ y ≤ q ∧ (q : ℝ) ≤ x)
    (hg0 : ∀ q : ℕ, q.Prime → y ≤ q → (q : ℝ) ≤ x → 0 ≤ g q)
    (hgB : ∀ q ∈ S, g q ≤ B) :
    ∑ q ∈ S, g q ≤ ∑ q ∈ Ioc ⌊y⌋₊ ⌊x⌋₊, (if q.Prime then g q else 0) + B := by
  rw [← sum_filter_add_sum_filter_not S (fun q => q ≤ ⌊y⌋₊)]
  have h1 : ∑ q ∈ S.filter (fun q => q ≤ ⌊y⌋₊), g q ≤ B := by
    have key : ∀ c ∈ S.filter (fun q => q ≤ ⌊y⌋₊), c = ⌊y⌋₊ := by
      intro c hc
      obtain ⟨hcS, hcy⟩ := mem_filter.mp hc
      have h1 : (c : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hcy
      have h2 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy
      have h3 := (hS c hcS).2.1
      have : (c : ℝ) = ⌊y⌋₊ := le_antisymm h1 (h2.trans h3)
      exact_mod_cast this
    have hc : (S.filter (fun q => q ≤ ⌊y⌋₊)).card ≤ 1 := by
      apply card_le_one.mpr
      intro a ha b hb
      rw [key a ha, key b hb]
    calc _ ≤ ∑ q ∈ S.filter (fun q => q ≤ ⌊y⌋₊), B :=
          sum_le_sum (fun q hq => hgB q (mem_filter.mp hq).1)
      _ = (S.filter (fun q => q ≤ ⌊y⌋₊)).card * B := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 1 * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hB
      _ = B := one_mul B
  have h2 : ∑ q ∈ S.filter (fun q => ¬ q ≤ ⌊y⌋₊), g q ≤
      ∑ q ∈ Ioc ⌊y⌋₊ ⌊x⌋₊, (if q.Prime then g q else 0) := by
    rw [← sum_filter]
    apply sum_le_sum_of_subset_of_nonneg
    · intro q hq
      obtain ⟨hqS, hqy⟩ := mem_filter.mp hq
      obtain ⟨hp, _, hqx⟩ := hS q hqS
      have hx : 0 ≤ x := le_trans (Nat.cast_nonneg q) hqx
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega, Nat.le_floor hqx⟩, hp⟩
    · intro q hq _
      obtain ⟨hq1, hp⟩ := mem_filter.mp hq
      have hlt := (mem_Ioc.mp hq1)
      have hx : 0 ≤ x := by
        by_contra hneg
        push_neg at hneg
        rw [Nat.floor_of_nonpos hneg.le] at hlt
        omega
      exact hg0 q hp ((Nat.floor_lt hy).mp hlt.1).le ((Nat.le_floor_iff hx).mp hlt.2)
  linarith

private theorem bsc3_inner_int (a α : ℝ) (hα : 0 < α) (h : 2 * α ≤ a) :
    ∫ v in α..(a / 2), (1 / (a - v)) / v = log ((a - α) / α) / a := by
  have ha : 0 < a := by linarith
  have hsub : ∀ v ∈ Set.uIcc α (a / 2), 0 < v ∧ 0 < a - v := by
    intro v hv
    rw [Set.uIcc_of_le (by linarith)] at hv
    exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hderiv : ∀ v ∈ Set.uIcc α (a / 2),
      HasDerivAt (fun v => (log v - log (a - v)) / a) ((1 / (a - v)) / v) v := by
    intro v hv
    obtain ⟨h1, h2⟩ := hsub v hv
    have d1 := hasDerivAt_log h1.ne'
    have d2 : HasDerivAt (fun v => log (a - v)) ((a - v)⁻¹ * (-1)) v := by
      have := ((hasDerivAt_id v).const_sub a)
      exact (hasDerivAt_log h2.ne').comp v (by simpa using this)
    convert (d1.sub d2).div_const a using 1
    field_simp
    ring
  have hcont : ContinuousOn (fun v => (1 / (a - v)) / v) (Set.uIcc α (a / 2)) := by
    apply ContinuousOn.div (ContinuousOn.div continuousOn_const (by fun_prop) ?_) continuousOn_id
    · intro v hv; exact (hsub v hv).1.ne'
    · intro v hv; exact (hsub v hv).2.ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  have e1 : a - a / 2 = a / 2 := by ring
  rw [e1, sub_self, zero_div, zero_sub, ← neg_div, neg_sub, log_div (by linarith) hα.ne']

private theorem bsc3_logratio_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2) :
    log a / (a + 1) ≤ log b / (b + 1) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have hl1 : log a ≤ a - 1 := log_le_sub_one_of_pos ha0
  have hl0 : 0 ≤ log a := log_nonneg ha
  have hlr : 1 - a / b ≤ log (b / a) := by
    have := one_sub_inv_le_log_of_pos (div_pos hb0 ha0)
    rwa [inv_div] at this
  rw [log_div hb0.ne' ha0.ne'] at hlr
  have hq : (b - a) / b ≤ log b - log a := by
    have : 1 - a / b = (b - a) / b := by field_simp
    linarith
  have hq' : (b - a) ≤ (log b - log a) * b := by
    rwa [div_le_iff₀ hb0] at hq
  -- need log a * (b + 1) ≤ log b * (a + 1), i.e. log a * (b - a) ≤ (log b - log a) * (a + 1)
  have hla : log a * b ≤ a + 1 := by nlinarith
  have hdiff : 0 ≤ log b - log a := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hq' hdiff, mul_nonneg hdiff hl0]
private lemma bsc3_exp_rpow (N : ℕ) (hN : 0 < N) (c : ℝ) : (N : ℝ) ^ c = exp (c * log N) := by
  rw [rpow_def_of_pos (by exact_mod_cast hN), mul_comm]

private lemma bsc3_z1 (N : ℕ) (hN : 0 < N) : z1 N = exp (1 / 11 * log N) := by
  show (N : ℝ) ^ (1 / 11 : ℝ) = _
  exact bsc3_exp_rpow N hN _

private lemma bsc3_z2 (N : ℕ) (hN : 0 < N) : z2 N = exp (100 / 329 * log N) := by
  show (N : ℝ) ^ (1 / 3.29 : ℝ) = _
  rw [bsc3_exp_rpow N hN]; norm_num

private lemma bsc3_lo {L a q : ℝ} (hL : 0 < L) (h : exp (a * L) ≤ q) : a ≤ log q / L := by
  rw [le_div_iff₀ hL]
  have := log_le_log (exp_pos _) h
  rwa [log_exp] at this

private lemma bsc3_hi {L b q : ℝ} (hL : 0 < L) (hq : 0 < q) (h : q ≤ exp (b * L)) :
    log q / L ≤ b := by
  rw [div_le_iff₀ hL]
  have := log_le_log hq h
  rwa [log_exp] at this

private lemma bsc3_hi' {L b q : ℝ} (hL : 0 < L) (hq : 0 < q) (h : q < exp (b * L)) :
    log q / L < b := by
  rw [div_lt_iff₀ hL]
  have := log_lt_log hq h
  rwa [log_exp] at this

private lemma bsc3_N_pos (N : ℕ) (hL : 0 < log (N : ℝ)) : 0 < N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp at hL
  · exact h

private lemma bsc3_exp_gt (c L : ℝ) : c * L < exp (c * L) := by
  linarith [add_one_le_exp (c * L)]

/-- The inner weight 1/(1 - u - v) of the all large pair sum. -/
private def bsc3_f (u v : ℝ) : ℝ := 1 / (1 - u - v)

/-- The inner integral of the all large pair sum, in closed form. -/
private def bsc3_G3 (u : ℝ) : ℝ := log ((1 - u - u) / u) / (1 - u)

private lemma bsc3_logratio_mono3 {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 2) :
    log a * (a + 2) / (a + 1) ≤ log b * (b + 2) / (b + 1) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have hl1 : log a ≤ a - 1 := log_le_sub_one_of_pos ha0
  have hl0 : 0 ≤ log a := log_nonneg ha
  have hlr : 1 - a / b ≤ log (b / a) := by
    have := one_sub_inv_le_log_of_pos (div_pos hb0 ha0)
    rwa [inv_div] at this
  rw [log_div hb0.ne' ha0.ne'] at hlr
  have hq : (b - a) / b ≤ log b - log a := by
    have : 1 - a / b = (b - a) / b := by field_simp
    linarith
  have hq' : (b - a) ≤ (log b - log a) * b := by
    rwa [div_le_iff₀ hb0] at hq
  have hdiff : 0 ≤ log b - log a := by nlinarith
  have hba : 0 ≤ b - a := by linarith
  have k1 : (b - a) * (a + 1) ≤ (log b - log a) * b * (a + 1) :=
    mul_le_mul_of_nonneg_right hq' (by linarith)
  have k2 : (log b - log a) * b * (a + 1) ≤ (log b - log a) * (b + 2) * (a + 1) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_left (by linarith) hdiff
  have k3 : log a * (b - a) ≤ (b - a) * (a + 1) := by nlinarith
  nlinarith

private lemma bsc3_G3_bounds (u : ℝ) (h1 : 100 / 329 ≤ u) (h2 : u ≤ 1 / 3) :
    0 ≤ bsc3_G3 u ∧ bsc3_G3 u ≤ 1 := by
  unfold bsc3_G3
  have hu0 : 0 < u := by linarith
  have hw1 : 1 ≤ (1 - u - u) / u := by
    rw [le_div_iff₀ hu0]; linarith
  have hw2 : (1 - u - u) / u ≤ 1.29 := by
    rw [div_le_iff₀ hu0]; linarith
  have hl0 := log_nonneg hw1
  have hl1 : log ((1 - u - u) / u) ≤ 0.29 := by
    have := log_le_sub_one_of_pos (show 0 < (1 - u - u) / u by linarith)
    linarith
  have hd : 0 < 1 - u := by linarith
  refine ⟨div_nonneg hl0 hd.le, ?_⟩
  rw [div_le_iff₀ hd]; linarith

private lemma bsc3_G3_anti : AntitoneOn bsc3_G3 (Set.Icc (100 / 329) (1 / 3)) := by
  intro a ha b hb hab
  have key : ∀ u, 100 / 329 ≤ u → u ≤ 1 / 3 → bsc3_G3 u =
      log ((1 - u - u) / u) * ((1 - u - u) / u + 2) / ((1 - u - u) / u + 1) := by
    intro u hu1 hu2
    have hu0 : u ≠ 0 := by intro h; linarith
    have hd : (1 - u) ≠ 0 := by intro h; linarith
    have e2 : (1 - u - u) / u + 2 = 1 / u := by field_simp; ring
    have e1 : (1 - u - u) / u + 1 = (1 - u) / u := by field_simp; ring
    have e : ((1 - u - u) / u + 2) / ((1 - u - u) / u + 1) = 1 / (1 - u) := by
      rw [e2, e1]; field_simp
    rw [mul_div_assoc, e]
    unfold bsc3_G3
    ring
  rw [key a ha.1 ha.2, key b hb.1 hb.2]
  have ha0 : 0 < a := by linarith [ha.1]
  have hb0 : 0 < b := by linarith [hb.1]
  apply bsc3_logratio_mono3
  · rw [le_div_iff₀ hb0]; linarith [hb.2]
  · rw [div_le_div_iff₀ hb0 ha0]; nlinarith
  · rw [div_le_iff₀ ha0]; linarith [ha.1]

/-- The all large pair region splits as an outer prime sum of inner prime sums. -/
private lemma bsc3_split (N : ℕ) (hN : 2 ≤ N) :
    log N * ∑ b ∈ switchedThreePairs306 N,
      1 / ((b.1 * b.2 : ℕ) * log ((N : ℝ) / (b.1 * b.2 : ℕ))) ≤
    ∑ p ∈ (range (N + 1)).filter
        (fun p : ℕ => p.Prime ∧ z2 N ≤ p ∧ (p : ℝ) ≤ exp (1 / 3 * log N)),
      (1 / (p : ℝ)) * ∑ q ∈ (range (N + 1)).filter
        (fun q : ℕ => q.Prime ∧ p < q ∧ (q : ℝ) < ((N : ℝ) / p) ^ (1 / 2 : ℝ)),
        bsc3_f (log p / log N) (log q / log N) / q := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hL : 0 < log (N : ℝ) := log_pos hNr
  have hsq : ∀ p q : ℕ, p.Prime → q.Prime → (q : ℝ) < ((N : ℝ) / p) ^ (1 / 2 : ℝ) →
      (p : ℝ) * q ^ 2 < N := by
    intro p q hp hq hqr
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
    rw [← sqrt_eq_rpow, lt_sqrt hq0.le] at hqr
    have h1 := (lt_div_iff₀ hp0).mp hqr
    linarith
  have hterm : ∀ p q : ℕ, p.Prime → q.Prime → (q : ℝ) < ((N : ℝ) / p) ^ (1 / 2 : ℝ) →
      log N * (1 / ((p * q : ℕ) * log ((N : ℝ) / (p * q : ℕ)))) =
        (1 / (p : ℝ)) * (bsc3_f (log p / log N) (log q / log N) / q) ∧
      0 ≤ (1 / (p : ℝ)) * (bsc3_f (log p / log N) (log q / log N) / q) := by
    intro p q hp hq hqr
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have h2 := hsq p q hp hq hqr
    have hpq : (p : ℝ) * q < N := by
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_lt.le
      nlinarith
    have hlog : log ((N : ℝ) / (p * q)) = log N - log p - log q := by
      rw [log_div (by linarith) (by positivity), log_mul hp0.ne' hq0.ne']; ring
    have hpos : 0 < log N - log p - log q := by
      rw [← hlog]; apply log_pos; rw [one_lt_div (by positivity)]; exact hpq
    have hden : 1 - log p / log N - log q / log N = (log N - log p - log q) / log N := by
      field_simp
    unfold bsc3_f
    rw [hden]
    push_cast
    rw [hlog]
    constructor
    · field_simp
    · have : 0 < (log N - log p - log q) / log N := div_pos hpos hL
      positivity
  have hcube : ∀ p q : ℕ, p.Prime → q.Prime → p < q →
      (q : ℝ) < ((N : ℝ) / p) ^ (1 / 2 : ℝ) → (p : ℝ) ≤ exp (1 / 3 * log N) := by
    intro p q hp hq hpq hqr
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have h2 := hsq p q hp hq hqr
    have hpqr : (p : ℝ) < q := by exact_mod_cast hpq
    have hpp : (p : ℝ) * p ≤ q * q := mul_le_mul hpqr.le hpqr.le hp0.le (by positivity)
    have h3 : (p : ℝ) ^ 3 < N := by
      have : (p : ℝ) ^ 3 = p * (p * p) := by ring
      rw [this]
      calc (p : ℝ) * (p * p) ≤ p * (q * q) := mul_le_mul_of_nonneg_left hpp hp0.le
        _ = p * q ^ 2 := by ring
        _ < N := h2
    have h4 : 3 * log (p : ℝ) < log N := by
      have := log_lt_log (by positivity) h3
      rw [log_pow] at this; push_cast at this; linarith
    rw [← exp_log hp0]
    apply exp_le_exp.mpr
    linarith
  unfold switchedThreePairs306
  rw [sum_filter, Finset.product_eq_sprod, sum_product, mul_sum, sum_filter]
  apply sum_le_sum
  intro p hp
  split_ifs with hpc
  · rw [mul_sum, mul_sum, sum_filter]
    apply sum_le_sum
    intro q hq
    by_cases h1 : (p.Prime ∧ q.Prime ∧ z2 N ≤ (p : ℝ) ∧ p < q ∧
        (q : ℝ) < ((N : ℝ) / (p : ℝ)) ^ (1 / 2 : ℝ) ∧ Nat.Coprime (p * q) N)
    · have h2 : q.Prime ∧ p < q ∧ (q : ℝ) < ((N : ℝ) / p) ^ (1 / 2 : ℝ) :=
        ⟨h1.2.1, h1.2.2.2.1, h1.2.2.2.2.1⟩
      rw [if_pos h1, if_pos h2]
      exact le_of_eq (hterm p q h1.1 h1.2.1 h1.2.2.2.2.1).1
    · rw [if_neg h1]
      split_ifs with h2
      · rw [mul_zero]
        exact (hterm p q hpc.1 h2.1 h2.2.2).2
      · simp
  · rw [mul_sum]
    apply le_of_eq
    apply sum_eq_zero
    intro q _
    rw [if_neg]
    · simp
    · intro h
      exact hpc ⟨h.1, h.2.2.1, hcube p q h.1 h.2.1 h.2.2.2.1 h.2.2.2.2.1⟩

/-- The inner prime sum of the all large region for one outer prime. -/
private lemma bsc3_inner (N : ℕ) (hL70 : 70 ≤ log (N : ℝ)) (K : ℕ) (hK : 0 < K) (p : ℕ)
    (hp : p.Prime) (hp1 : z2 N ≤ p) (hp2 : (p : ℝ) ≤ exp (1 / 3 * log N)) :
    ∑ q ∈ (range (N + 1)).filter
        (fun q : ℕ => q.Prime ∧ p < q ∧ (q : ℝ) < ((N : ℝ) / p) ^ (1 / 2 : ℝ)),
      bsc3_f (log p / log N) (log q / log N) / q ≤
      bsc3_G3 (log p / log N) + (3 / K + 40 * K / log N) := by
  set L := log (N : ℝ) with hLdef
  have hL : 0 < L := by linarith
  have hN0 : 0 < N := bsc3_N_pos N hL
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [bsc3_z2 N hN0] at hp1
  set u := log p / L with hu
  have hu1 : 100 / 329 ≤ u := bsc3_lo hL hp1
  have hu2 : u ≤ 1 / 3 := bsc3_hi hL hp0 hp2
  have huL : u * L = log p := by rw [hu]; field_simp
  set β := (1 - u) / 2 with hβ
  have hroot : ((N : ℝ) / p) ^ (1 / 2 : ℝ) = exp (β * L) := by
    rw [rpow_def_of_pos (div_pos (by exact_mod_cast hN0) hp0), log_div (by positivity) hp0.ne',
      ← huL, hβ]
    congr 1; ring
  have hαβ : u ≤ β := by rw [hβ]; linarith
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hfpos : ∀ v, v ≤ β → (1 - u) / 2 ≤ 1 - u - v := by intro v hv; rw [hβ] at hv; linarith
  have hf3 : ∀ v, v ≤ β → bsc3_f u v ≤ 3 := by
    intro v hv
    have := hfpos v hv
    unfold bsc3_f
    rw [div_le_iff₀ (by linarith)]; linarith
  have hf0 : ∀ v, v ≤ β → 0 ≤ bsc3_f u v := by
    intro v hv
    have := hfpos v hv
    unfold bsc3_f
    exact (div_pos one_pos (by linarith)).le
  have hfloor : ⌊exp (u * L)⌋₊ = p := by rw [huL, exp_log hp0, Nat.floor_natCast]
  have hsub : ∑ q ∈ (range (N + 1)).filter
        (fun q : ℕ => q.Prime ∧ p < q ∧ (q : ℝ) < ((N : ℝ) / p) ^ (1 / 2 : ℝ)),
      bsc3_f u (log q / L) / q ≤
      ∑ q ∈ Ioc ⌊exp (u * L)⌋₊ ⌊exp (β * L)⌋₊,
        (if q.Prime then bsc3_f u (log q / L) / q else 0) := by
    rw [← sum_filter, hfloor]
    apply sum_le_sum_of_subset_of_nonneg
    · intro q hq
      obtain ⟨_, h1, h2, h3⟩ := mem_filter.mp hq
      rw [hroot] at h3
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨h2, Nat.le_floor h3.le⟩, h1⟩
    · intro q hq _
      obtain ⟨hq1, _⟩ := mem_filter.mp hq
      have hlt := mem_Ioc.mp hq1
      have hq0 : (0 : ℝ) < q := by
        have : 0 < q := lt_of_le_of_lt (Nat.zero_le p) hlt.1
        exact_mod_cast this
      have hqx : (q : ℝ) ≤ exp (β * L) := (Nat.le_floor_iff (exp_pos _).le).mp hlt.2
      exact div_nonneg (hf0 _ (bsc3_hi hL hq0 hqx)) hq0.le
  have hlog2 : log 2 ≤ u * L := by
    rw [huL]
    exact log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
  have hmono : MonotoneOn (bsc3_f u) (Set.Icc u β) := by
    intro a ha b hb hab
    have h1 := hfpos a ha.2
    have h2 := hfpos b hb.2
    unfold bsc3_f
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hm := bsc3_mono_sum L u β K hK hL (by linarith) hαβ hlog2 (bsc3_f u) hmono
    (fun v hv => hf0 v hv.2)
  have hint : ∫ v in u..β, bsc3_f u v / v = bsc3_G3 u := by
    unfold bsc3_f bsc3_G3
    rw [hβ]
    exact bsc3_inner_int (1 - u) u (by linarith) (by linarith)
  rw [hint] at hm
  have hu0 : 0 < u := by linarith
  have hratio : log (β / u) / K ≤ 1 / K := by
    apply div_le_div_of_nonneg_right _ hKr.le
    have := log_le_sub_one_of_pos (show 0 < β / u from div_pos (by linarith) hu0)
    have : β / u ≤ 2 := by rw [div_le_iff₀ hu0]; rw [hβ]; linarith
    linarith
  have hratio0 : 0 ≤ log (β / u) / K :=
    div_nonneg (log_nonneg (by rw [le_div_iff₀ hu0]; linarith)) hKr.le
  have hdiff : (bsc3_f u β - bsc3_f u u) * (log (β / u) / K) ≤ 3 / K := by
    have h1 : bsc3_f u β - bsc3_f u u ≤ 3 := by
      linarith [hf3 β le_rfl, hf0 u hαβ]
    calc _ ≤ 3 * (1 / (K : ℝ)) := mul_le_mul h1 hratio hratio0 (by norm_num)
      _ = 3 / (K : ℝ) := by ring
  have hlast : (K : ℝ) * bsc3_f u β * (4 / (u * L)) ≤ 40 * K / L := by
    have := hf3 β le_rfl
    have h0 := hf0 β le_rfl
    calc (K : ℝ) * bsc3_f u β * (4 / (u * L)) ≤ K * 3 * (4 / (100 / 329 * L)) := by
          apply mul_le_mul _ _ (div_pos (by norm_num) (mul_pos hu0 hL)).le (by positivity)
          · exact mul_le_mul_of_nonneg_left this hKr.le
          · exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
              (mul_le_mul_of_nonneg_right hu1 hL.le)
      _ = 39.48 * K / L := by field_simp; ring
      _ ≤ 40 * K / L := by
          apply div_le_div_of_nonneg_right _ hL.le; nlinarith
  linarith

/-- The outer prime sum of the all large region against its integral. -/
private lemma bsc3_outer (N : ℕ) (hL70 : 70 ≤ log (N : ℝ)) (K : ℕ) (hK : 0 < K) :
    ∑ p ∈ (range (N + 1)).filter
        (fun p : ℕ => p.Prime ∧ z2 N ≤ p ∧ (p : ℝ) ≤ exp (1 / 3 * log N)),
      (1 / (p : ℝ)) * ∑ q ∈ (range (N + 1)).filter
        (fun q : ℕ => q.Prime ∧ p < q ∧ (q : ℝ) < ((N : ℝ) / p) ^ (1 / 2 : ℝ)),
        bsc3_f (log p / log N) (log q / log N) / q ≤
      (∫ u in (100 / 329 : ℝ)..(1 / 3), bsc3_G3 u / u) +
        (11 / K + 168 * K / log N + 42 / log N) := by
  have hL : 0 < log (N : ℝ) := by linarith
  have hN0 : 0 < N := bsc3_N_pos N hL
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  set E1 : ℝ := 3 / K + 40 * K / log N with hE1
  have hE10 : 0 ≤ E1 := by positivity
  set P1 := (range (N + 1)).filter
    (fun p : ℕ => p.Prime ∧ z2 N ≤ p ∧ (p : ℝ) ≤ exp (1 / 3 * log N)) with hP1
  have hstep : ∑ p ∈ P1, (1 / (p : ℝ)) * ∑ q ∈ (range (N + 1)).filter
        (fun q : ℕ => q.Prime ∧ p < q ∧ (q : ℝ) < ((N : ℝ) / p) ^ (1 / 2 : ℝ)),
        bsc3_f (log p / log N) (log q / log N) / q ≤
      ∑ p ∈ P1, bsc3_G3 (log p / log N) / p + E1 * ∑ p ∈ P1, (1 / (p : ℝ)) := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro p hp
    obtain ⟨_, hpp, hp1, hp2⟩ := mem_filter.mp hp
    have h := bsc3_inner N hL70 K hK p hpp hp1 hp2
    have hp0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    calc _ ≤ (1 / (p : ℝ)) * (bsc3_G3 (log p / log N) + E1) := mul_le_mul_of_nonneg_left h hp0
      _ = _ := by ring
  have hP1' : P1 = (range (N + 1)).filter (fun p : ℕ => p.Prime ∧ exp (100 / 329 * log N) ≤ p ∧
      (p : ℝ) ≤ exp (1 / 3 * log N)) := by
    rw [hP1, bsc3_z2 N hN0]
  have hS : ∀ p ∈ P1, p.Prime ∧ exp (100 / 329 * log N) ≤ (p : ℝ) ∧
      (p : ℝ) ≤ exp (1 / 3 * log N) := by
    intro p hp
    rw [hP1'] at hp
    obtain ⟨_, h1, h2, h3⟩ := mem_filter.mp hp
    exact ⟨h1, h2, h3⟩
  have hlog2 : log 2 ≤ 100 / 329 * log N := by
    have := log_two_lt_d9; linarith
  have hbd1 : 1 / exp (100 / 329 * log N) ≤ 3.29 / log N := by
    have := bsc3_exp_gt (100 / 329) (log N)
    calc 1 / exp (100 / 329 * log N) ≤ 1 / (100 / 329 * log N) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) this.le
      _ = 3.29 / log N := by field_simp; ring
  have hrec : ∑ p ∈ P1, (1 / (p : ℝ)) ≤ 2 := by
    have hb := bsc3_bdry P1 (exp (100 / 329 * log N)) (exp (1 / 3 * log N))
      (1 / exp (100 / 329 * log N)) (fun p => 1 / (p : ℝ)) (exp_pos _).le (by positivity) hS
      (fun q _ _ _ => by positivity)
      (fun q hq => div_le_div_of_nonneg_left (by norm_num) (exp_pos _) (hS q hq).2.1)
    have hm := bsc3_mono_sum (log N) (100 / 329) (1 / 3) 1 one_pos hL (by norm_num) (by norm_num)
      hlog2 (fun _ => (1 : ℝ)) (fun _ _ _ _ _ => le_rfl) (fun _ _ => zero_le_one)
    beta_reduce at hm
    rw [integral_one_div_of_pos (by norm_num) (by norm_num)] at hm
    have hlb : log ((1 / 3 : ℝ) / (100 / 329)) ≤ 1 := by
      have := log_le_sub_one_of_pos (show (0 : ℝ) < (1 / 3) / (100 / 329) by norm_num)
      norm_num at this ⊢; linarith
    have h44 : (((1 : ℕ) : ℝ)) * 1 * (4 / (100 / 329 * log N)) = 13.16 / log N := by
      field_simp; ring
    rw [h44] at hm
    have h55 : 13.16 / log N + 3.29 / log N ≤ 0.5 := by
      rw [← add_div, div_le_iff₀ hL]; linarith
    linarith
  have hmain : ∑ p ∈ P1, bsc3_G3 (log p / log N) / p ≤
      (∫ u in (100 / 329 : ℝ)..(1 / 3), bsc3_G3 u / u) + 1 / K + 14 * K / log N +
        4 / log N := by
    have hb := bsc3_bdry P1 (exp (100 / 329 * log N)) (exp (1 / 3 * log N))
      (1 / exp (100 / 329 * log N)) (fun p => bsc3_G3 (log p / log N) / p) (exp_pos _).le
      (by positivity) hS
      (fun q _ hq1 hq2 => by
        have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (exp_pos _) hq1
        exact div_nonneg (bsc3_G3_bounds _ (bsc3_lo hL hq1) (bsc3_hi hL hq0 hq2)).1 hq0.le)
      (fun q hq => by
        obtain ⟨_, hq1, hq2⟩ := hS q hq
        have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (exp_pos _) hq1
        have hG := (bsc3_G3_bounds _ (bsc3_lo hL hq1) (bsc3_hi hL hq0 hq2)).2
        calc bsc3_G3 (log q / log N) / q ≤ 1 / q := div_le_div_of_nonneg_right hG hq0.le
          _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (exp_pos _) hq1)
    have ha := bsc3_anti_sum (log N) (100 / 329) (1 / 3) K hK hL (by norm_num) (by norm_num)
      hlog2 bsc3_G3 bsc3_G3_anti (fun v hv => (bsc3_G3_bounds v hv.1 hv.2).1)
    have hG1 := bsc3_G3_bounds (100 / 329) le_rfl (by norm_num)
    have hG2 := bsc3_G3_bounds (1 / 3) (by norm_num) le_rfl
    have hlr : log ((1 / 3 : ℝ) / (100 / 329)) / K ≤ 1 / K := by
      apply div_le_div_of_nonneg_right _ hKr.le
      have := log_le_sub_one_of_pos (show (0 : ℝ) < (1 / 3) / (100 / 329) by norm_num)
      norm_num at this ⊢; linarith
    have hlr0 : 0 ≤ log ((1 / 3 : ℝ) / (100 / 329)) / K :=
      div_nonneg (log_nonneg (by norm_num)) hKr.le
    have hd1 : (bsc3_G3 (100 / 329) - bsc3_G3 (1 / 3)) * (log ((1 / 3 : ℝ) / (100 / 329)) / K)
        ≤ 1 / K := by
      calc _ ≤ 1 * (1 / (K : ℝ)) := mul_le_mul (by linarith) hlr hlr0 (by norm_num)
        _ = 1 / (K : ℝ) := one_mul _
    have hd2 : (K : ℝ) * bsc3_G3 (100 / 329) * (4 / (100 / 329 * log N)) ≤ 14 * K / log N := by
      calc (K : ℝ) * bsc3_G3 (100 / 329) * (4 / (100 / 329 * log N)) ≤
            K * 1 * (4 / (100 / 329 * log N)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hG1.2 hKr.le
        _ = 13.16 * K / log N := by field_simp; ring
        _ ≤ 14 * K / log N := by
            apply div_le_div_of_nonneg_right _ hL.le; nlinarith
    have hbd2 : 1 / exp (100 / 329 * log N) ≤ 4 / log N :=
      hbd1.trans (div_le_div_of_nonneg_right (by norm_num) hL.le)
    linarith
  refine hstep.trans ?_
  have hE : E1 * ∑ p ∈ P1, (1 / (p : ℝ)) ≤ E1 * 2 := mul_le_mul_of_nonneg_left hrec hE10
  have hE2 : E1 * 2 = 6 / K + 80 * K / log N := by rw [hE1]; ring
  have hk1 : 0 ≤ 4 / (K : ℝ) := by positivity
  have hk2 : 0 ≤ 74 * (K : ℝ) / log N := by positivity
  have hk3 : 0 ≤ 38 / log (N : ℝ) := by positivity
  have h11 : 1 / (K : ℝ) + 6 / K + 4 / K = 11 / K := by ring
  have h168 : 14 * (K : ℝ) / log N + 80 * K / log N + 74 * K / log N = 168 * K / log N := by ring
  have h42 : 4 / log (N : ℝ) + 38 / log N = 42 / log N := by ring
  linarith

private lemma bsc3_integral :
    (∫ u in (100 / 329 : ℝ)..(1 / 3), bsc3_G3 u / u) =
      ∫ t in (2 : ℝ)..2.29, log (t - 1) / t := by
  set h : ℝ → ℝ := fun s => bsc3_G3 s / s with hh
  have hf : ∀ x ∈ Set.uIcc (2 : ℝ) 2.29,
      HasDerivAt (fun t => 1 / (t + 1)) (-1 / (x + 1) ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    have hx1 : x + 1 ≠ 0 := by have := hx.1; intro h'; linarith
    have := ((hasDerivAt_id x).add_const 1).inv hx1
    simp only [one_div]
    convert this using 1 <;> first | (funext t; simp) | simp
  have hf' : ContinuousOn (fun x : ℝ => -1 / (x + 1) ^ 2) (Set.uIcc (2 : ℝ) 2.29) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx; rw [Set.uIcc_of_le (by norm_num)] at hx; have := hx.1; positivity
  have himg : (fun t : ℝ => 1 / (t + 1)) '' Set.uIcc (2 : ℝ) 2.29 ⊆
      Set.Icc (100 / 329) (1 / 3) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Set.uIcc_of_le (by norm_num)] at ht
    obtain ⟨ht1, ht2⟩ := ht
    constructor
    · rw [div_le_div_iff₀ (by norm_num) (by linarith)]; linarith
    · rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hcont : ContinuousOn h (Set.Icc (100 / 329) (1 / 3)) := by
    simp only [hh]
    unfold bsc3_G3
    have hs0 : ∀ s ∈ Set.Icc (100 / 329 : ℝ) (1 / 3), s ≠ 0 := by
      intro s hs; have := hs.1; intro h'; linarith
    apply ContinuousOn.div _ continuousOn_id hs0
    apply ContinuousOn.div _ (by fun_prop)
    · intro s hs; have := hs.2; intro h'; linarith
    apply ContinuousOn.log (ContinuousOn.div (by fun_prop) continuousOn_id hs0)
    intro s hs
    have h1 := hs.1
    have h2 := hs.2
    have : 0 < (1 - s - s) / s := div_pos (by linarith) (by linarith)
    exact this.ne'
  have hg : ContinuousOn (fun s => -h s) ((fun t : ℝ => 1 / (t + 1)) '' Set.uIcc (2 : ℝ) 2.29) :=
    (hcont.neg).mono himg
  have key := intervalIntegral.integral_comp_mul_deriv' hf hf' hg
  have hR : ∫ t in (2 : ℝ)..2.29, log (t - 1) / t =
      ∫ t in (2 : ℝ)..2.29, ((fun s => -h s) ∘ (fun t => 1 / (t + 1))) t * (-1 / (t + 1) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have ht0 : t ≠ 0 := by have := ht.1; intro h'; linarith
    have ht1 : t + 1 ≠ 0 := by have := ht.1; intro h'; linarith
    simp only [Function.comp, hh]
    unfold bsc3_G3
    have e1 : (1 - 1 / (t + 1) - 1 / (t + 1)) / (1 / (t + 1)) = t - 1 := by
      field_simp; ring
    rw [e1]
    have e2 : 1 - 1 / (t + 1) = t / (t + 1) := by field_simp; ring
    rw [e2]
    field_simp
  rw [hR, key, show (1 : ℝ) / (2 + 1) = 1 / 3 by norm_num,
    show (1 : ℝ) / (2.29 + 1) = 100 / 329 by norm_num, intervalIntegral.integral_neg,
    intervalIntegral.integral_symm (100 / 329 : ℝ) (1 / 3), neg_neg]

/-- LEAF. Page 604 display 4.15, the all large prime pair sum to its integral.
This has no S3 count and no switched remainder. The order p1 less than p2
is retained. Coprimality with N permits an upper limit with every reserve. -/
theorem leaf337_three_pair_sum :
    ∀ δ : ℝ, 0 < δ → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      sieveThreePairSum337 N ≤ sieveThreeCoefficient337 + δ := by
  intro δ hδ
  set c : ℝ := 8 / (2 * (0.95 : ℝ) - 1) with hc
  have hc0 : 0 < c := by norm_num [hc]
  have hc9 : c ≤ 9 := by norm_num [hc]
  set K : ℕ := ⌈200 / δ⌉₊ + 1 with hKdef
  have hK : 0 < K := Nat.succ_pos _
  have hKr : (200 / δ : ℝ) ≤ K := by
    rw [hKdef]; push_cast; linarith [Nat.le_ceil (200 / δ)]
  set L0 : ℝ := 70 + 18 * (168 * K + 42) / δ with hL0
  refine ⟨⌈exp L0⌉₊ + 2, fun N hN => ?_⟩
  have hNe : exp L0 ≤ (N : ℝ) := by
    have := Nat.le_ceil (exp L0)
    have h2 : ((⌈exp L0⌉₊ + 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
    push_cast at h2; linarith
  have hN2 : 2 ≤ N := by omega
  have hLL : L0 ≤ log N := by
    have := log_le_log (exp_pos _) hNe; rwa [log_exp] at this
  have hq0 : 0 ≤ 18 * (168 * (K : ℝ) + 42) / δ := by positivity
  have hL70 : 70 ≤ log (N : ℝ) := by linarith
  have hL : 0 < log (N : ℝ) := by linarith
  have hmain := (bsc3_split N hN2).trans (bsc3_outer N hL70 K hK)
  unfold sieveThreePairSum337 sieveThreeCoefficient337
  rw [← hc, ← bsc3_integral, mul_assoc]
  have herr : c * (11 / K + 168 * K / log N + 42 / log N) ≤ δ := by
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
    have hKd : 200 ≤ (K : ℝ) * δ := by rwa [div_le_iff₀ hδ] at hKr
    have e1 : 11 / (K : ℝ) ≤ 11 * δ / 200 := by
      rw [div_le_iff₀ hKpos]; nlinarith
    have e2 : 168 * K / log N + 42 / log N ≤ δ / 18 := by
      rw [← add_div, div_le_iff₀ hL]
      have h3 : 18 * (168 * (K : ℝ) + 42) / δ ≤ log N := by linarith
      rw [div_le_iff₀ hδ] at h3
      nlinarith
    have hpos : 0 ≤ 11 / (K : ℝ) + 168 * K / log N + 42 / log N := by positivity
    calc c * (11 / K + 168 * K / log N + 42 / log N) ≤
          9 * (11 / K + 168 * K / log N + 42 / log N) := mul_le_mul_of_nonneg_right hc9 hpos
      _ ≤ 9 * (11 * δ / 200 + δ / 18) := by nlinarith
      _ ≤ δ := by nlinarith
  have h4 := mul_le_mul_of_nonneg_left hmain hc0.le
  have h5 : c * ((∫ u in (100 / 329 : ℝ)..(1 / 3), bsc3_G3 u / u) +
      (11 / K + 168 * K / log N + 42 / log N)) =
      c * (∫ u in (100 / 329 : ℝ)..(1 / 3), bsc3_G3 u / u) +
      c * (11 / K + 168 * K / log N + 42 / log N) := by ring
  linarith

/-! ### Split of the all large switching leaf, route burst 2026-11-12 -/

/-- The mass X for the all large region, page 604 display 4.15 with page 603. -/
def sw3X337 (N : ℕ) : ℝ := ∑ e ∈ switchedThreeE306 N, switchedLiTerm337 N e

/-- The coprime part of the remainder R1 at one modulus, page 603 display 4.10. -/
def sw3Wu337 (N d : ℕ) : ℝ :=
  |∑ e ∈ (switchedThreeE306 N).filter (fun e => e.Coprime d),
    ((switchedLocalCount337 N e d : ℝ) - switchedLiTerm337 N e / d.totient)|

/-- CITED. Page 604 display 4.15 by the analogue of page 603 display 4.12, Lemma 4 of page 599, Wu 1993,
https://doi.org/10.1093/qmath/44.1.109, applied to the all large switched coefficient, with constants uniform in N. The lab's WuMeanValue118 interface lets the
constants depend on the coefficient sequence, see wu_uniformity_obstruction118, so
this uniform form is stated as its own cited input. -/
theorem leaf337_three_wu_uniform (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (∑ d ∈ (Icc 1 ⌊sw2Level337 N B⌋₊).filter (fun d => N.Coprime d), sw3Wu337 N d) ≤
        K * (N : ℝ) ^ (0.95 : ℝ) / log N ^ A := by
  sorry

/-- The Li mass X of page 603 is at most the weighted prime pair sum times N^θ.
Each Li difference is at most its length over the logarithm of the left end; the
endpoint N - N^θ changes the logarithm by a bounded amount. The sum over the product
set E is at most the sum over the prime pairs. Page 604 display 4.13. -/
theorem sw3X_upper337 (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, sw3X337 N ≤ (1 + η) * ((N : ℝ) ^ (0.95 : ℝ) *
      ∑ b ∈ switchedThreePairs306 N, 1 / ((b.1 * b.2 : ℕ) * log ((N : ℝ) / (b.1 * b.2 : ℕ)))) := by
  classical
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp05 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.05)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hp13 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hp05.eventually_ge_atTop 2, hp13.eventually_ge_atTop 4,
    hlog.eventually_ge_atTop (3 * (1 + η) * log 2 / η), eventually_ge_atTop 2]
    with N h05 h13 hlN hN2
  simp only [Function.comp_def] at h05 h13
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hLp : 0 < log (N : ℝ) := log_pos hN1
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  set f : ℕ → ℝ := fun e => 1 / ((e : ℝ) * log ((N : ℝ) / e)) with hf
  have hrange : ∀ e ∈ switchedThreeE306 N, (0 : ℝ) < e ∧ (e : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ) := by
    intro e he
    have h := switchedThreeE_range337 N e hN2 he
    exact ⟨by exact_mod_cast h.1, h.2⟩
  have hNe : ∀ e ∈ switchedThreeE306 N, (N : ℝ) ^ (1 / 3 : ℝ) ≤ (N : ℝ) / e := by
    intro e he
    obtain ⟨_, h2⟩ := hrange e he
    have hep : (0 : ℝ) < e := (hrange e he).1
    rw [le_div_iff₀ hep]
    have hsplit : (N : ℝ) = (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) := by
      rw [← rpow_add hNp]; norm_num
    calc (N : ℝ) ^ (1 / 3 : ℝ) * e ≤ (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_left h2.le (rpow_pos_of_pos hNp _).le
      _ = N := hsplit.symm
  have hlogNe : ∀ e ∈ switchedThreeE306 N, log N / 3 ≤ log ((N : ℝ) / e) := by
    intro e he
    have h := log_le_log (rpow_pos_of_pos hNp _) (hNe e he)
    rw [log_rpow hNp] at h
    linarith
  have hterm : ∀ e ∈ switchedThreeE306 N,
      switchedLiTerm337 N e ≤ (1 + η) * ((N : ℝ) ^ (0.95 : ℝ) * f e) := by
    intro e he
    have hep : (0 : ℝ) < e := (hrange e he).1
    have hhalf : (N : ℝ) ^ (0.95 : ℝ) * 2 ≤ N := by
      have hsplit : (N : ℝ) = (N : ℝ) ^ (0.95 : ℝ) * (N : ℝ) ^ (0.05 : ℝ) := by
        rw [← rpow_add hNp]; norm_num
      calc (N : ℝ) ^ (0.95 : ℝ) * 2 ≤ (N : ℝ) ^ (0.95 : ℝ) * (N : ℝ) ^ (0.05 : ℝ) :=
            mul_le_mul_of_nonneg_left h05 (rpow_pos_of_pos hNp _).le
        _ = N := hsplit.symm
    set a : ℝ := ((N : ℝ) - (N : ℝ) ^ (0.95 : ℝ)) / e with ha
    have ha2 : (N : ℝ) / e / 2 ≤ a := by
      rw [ha, div_div, le_div_iff₀ hep]
      field_simp
      linarith
    have hNe4 : 4 ≤ (N : ℝ) / e := h13.trans (hNe e he)
    have hA2 : 2 ≤ a := by linarith
    have hab : a ≤ (N : ℝ) / e := by
      rw [ha]
      apply div_le_div_of_nonneg_right _ hep.le
      linarith [rpow_pos_of_pos hNp (0.95 : ℝ)]
    have hli := li_diff_le337 a ((N : ℝ) / e) hA2 hab
    have hlen : (N : ℝ) / e - a = (N : ℝ) ^ (0.95 : ℝ) / e := by
      rw [ha]; field_simp; ring
    have hloga : log ((N : ℝ) / e) - log 2 ≤ log a := by
      have h := log_le_log (by positivity) ha2
      rw [log_div (by positivity) (by norm_num)] at h
      exact h
    have hLe := hlogNe e he
    have hηl : (1 + η) * log 2 ≤ η * (log N / 3) := by
      have := (div_le_iff₀ hη).mp hlN
      linarith
    have hkey : log ((N : ℝ) / e) ≤ (1 + η) * log a := by
      have h1 : η * (log N / 3) ≤ η * log ((N : ℝ) / e) := mul_le_mul_of_nonneg_left hLe hη.le
      nlinarith
    have hlogap : 0 < log a := log_pos (by linarith)
    have hlogNep : 0 < log ((N : ℝ) / e) := by
      have : 0 < log N / 3 := by positivity
      linarith
    unfold switchedLiTerm337
    rw [← ha]
    calc li118 ((N : ℝ) / e) - li118 a ≤ ((N : ℝ) / e - a) / log a := hli
      _ = (N : ℝ) ^ (0.95 : ℝ) / e / log a := by rw [hlen]
      _ ≤ (1 + η) * ((N : ℝ) ^ (0.95 : ℝ) * f e) := by
        rw [hf]
        dsimp only
        rw [div_le_iff₀ hlogap]
        have hid : (1 + η) * ((N : ℝ) ^ (0.95 : ℝ) * (1 / ((e : ℝ) * log ((N : ℝ) / e)))) *
            log a = ((N : ℝ) ^ (0.95 : ℝ) / e) * ((1 + η) * log a / log ((N : ℝ) / e)) := by
          field_simp
        rw [hid]
        have hq : 1 ≤ (1 + η) * log a / log ((N : ℝ) / e) := by
          rw [le_div_iff₀ hlogNep]; linarith
        have hpos : 0 ≤ (N : ℝ) ^ (0.95 : ℝ) / e := by positivity
        nlinarith
  have hf0 : ∀ e ∈ switchedThreeE306 N, 0 ≤ f e := by
    intro e he
    have hep : (0 : ℝ) < e := (hrange e he).1
    have : 0 < log ((N : ℝ) / e) := by
      have := hlogNe e he
      have : 0 < log N / 3 := by positivity
      linarith
    rw [hf]; positivity
  have himg : (∑ e ∈ switchedThreeE306 N, f e) ≤
      ∑ b ∈ switchedThreePairs306 N, f (b.1 * b.2) := by
    unfold switchedThreeE306
    calc (∑ e ∈ (switchedThreePairs306 N).image (fun b => b.1 * b.2), f e) ≤
          ∑ e ∈ (switchedThreePairs306 N).image (fun b => b.1 * b.2),
            ∑ b ∈ (switchedThreePairs306 N).filter (fun b => b.1 * b.2 = e), f (b.1 * b.2) := by
          apply Finset.sum_le_sum
          intro e he
          obtain ⟨b, hb, hbe⟩ := mem_image.mp he
          have hmem : b ∈ (switchedThreePairs306 N).filter (fun b => b.1 * b.2 = e) :=
            Finset.mem_filter.mpr ⟨hb, hbe⟩
          have hnn : ∀ c ∈ (switchedThreePairs306 N).filter (fun b => b.1 * b.2 = e),
              0 ≤ f (c.1 * c.2) := by
            intro c hc
            obtain ⟨hc1, hc2⟩ := Finset.mem_filter.mp hc
            rw [hc2]
            exact hf0 e he
          have h := Finset.single_le_sum hnn hmem
          rw [hbe] at h
          exact h
      _ = ∑ b ∈ switchedThreePairs306 N, f (b.1 * b.2) :=
          Finset.sum_fiberwise_of_maps_to (fun b hb => mem_image_of_mem _ hb) _
  unfold sw3X337
  have hNpow : 0 ≤ (N : ℝ) ^ (0.95 : ℝ) := (rpow_pos_of_pos hNp _).le
  calc (∑ e ∈ switchedThreeE306 N, switchedLiTerm337 N e) ≤
        ∑ e ∈ switchedThreeE306 N, (1 + η) * ((N : ℝ) ^ (0.95 : ℝ) * f e) :=
        Finset.sum_le_sum hterm
    _ = (1 + η) * ((N : ℝ) ^ (0.95 : ℝ) * ∑ e ∈ switchedThreeE306 N, f e) := by
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ (1 + η) * ((N : ℝ) ^ (0.95 : ℝ) * ∑ b ∈ switchedThreePairs306 N, f (b.1 * b.2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left himg hNpow) (by linarith)
    _ = _ := by rw [hf]

#print axioms sw3X_upper337

set_option maxHeartbeats 1600000 in
/-- Page 604 display 4.15, first line: the main term of the analogous switching
argument for the all large region. The linear sieve main term F(s) X V is at most the
weighted all large prime pair sum. Same proof as leaf337_two_main_term. -/
theorem leaf337_three_main_term (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 100000 ∧ ∀ B k : ℝ, 0 < B → 0 < k →
      ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
        upperPhi337 ε (sw2Param337 N B k) * sw3X337 N * sw2V337 N B ≤
          (sieveThreePairSum337 N + δ) * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
  classical
  obtain ⟨nP, hPb⟩ := leaf337_three_pair_sum 1 one_pos
  set Pa : ℝ := |sieveThreeCoefficient337 + 1| + 1 with hPa
  have hPa0 : 0 < Pa := by positivity
  set η : ℝ := min (1 / 2) (δ / (15 * Pa)) with hηdef
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 / 2 := min_le_left _ _
  have hηδ : 15 * η * Pa ≤ δ := by
    have h := min_le_right (1 / 2 : ℝ) (δ / (15 * Pa))
    rw [← hηdef, le_div_iff₀ (by positivity)] at h
    linarith
  have hγ : 0 < exp eulerMascheroniConstant := exp_pos _
  set ε : ℝ := min (1 / 100000) (η * exp eulerMascheroniConstant / 106) with hεdef
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε ≤ 1 / 100000 := min_le_left _ _
  have hε2 : ε ≤ η * exp eulerMascheroniConstant / 106 := min_le_right _ _
  refine ⟨ε, hε0, hε1, fun B k hB hk => ?_⟩
  have hlogN : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hall : ∀ᶠ N : ℕ in atTop, Even N →
      upperPhi337 ε (sw2Param337 N B k) * sw3X337 N * sw2V337 N B ≤
        (sieveThreePairSum337 N + δ) * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
    filter_upwards [sw2V_upper337 B hB η hη0 (by linarith), sw3X_upper337 η hη0,
      sw2_level_bounds337 B hB, hlogN.eventually_ge_atTop (16 * (|log k| + 1) / η + 8),
      eventually_ge_atTop nP, eventually_ge_atTop (3 : ℕ)] with N hV hX hLb hlN hNP hN3
    intro he
    have hN2 : 2 ≤ N := by omega
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hLp : 0 < log (N : ℝ) := log_pos hN1
    have hC : 0 < C N := by
      unfold C
      exact mul_pos LeanLab.ChenExplicit.twinC_pos
        (lt_of_lt_of_le zero_lt_one (LeanLab.ChenExplicit.one_le_oddFactor N))
    set L : ℝ := sw2Level337 N B with hLdef
    have hL1 : 1 < L := lt_of_lt_of_le (one_lt_rpow hN1 (by norm_num)) hLb.1
    have hlogL : log N / 4 ≤ log L := by
      have := log_le_log (rpow_pos_of_pos hNp _) hLb.1
      rw [log_rpow hNp] at this
      linarith
    have hlogLp : 0 < log L := log_pos hL1
    have hsmall : 4 * |log k| ≤ η * log L := by
      have h1 := (div_le_iff₀ hη0).mp (show 16 * (|log k| + 1) / η ≤ log N - 8 by linarith)
      have h2 : η * (log N / 4) ≤ η * log L := mul_le_mul_of_nonneg_left hlogL hη0.le
      nlinarith [abs_nonneg (log k)]
    have hs := sw2_param_eq337 N B k hk hL1
    set s : ℝ := sw2Param337 N B k with hsdef
    have hs_lo : 2 - η / 2 ≤ s := by
      rw [hs]
      have : 2 * log k / log L ≤ η / 2 := by
        rw [div_le_iff₀ hlogLp]; linarith [le_abs_self (log k)]
      linarith
    have hs_hi : s ≤ 2 + η / 2 := by
      rw [hs]
      have : -(η / 2) ≤ 2 * log k / log L := by
        rw [le_div_iff₀ hlogLp]; linarith [neg_abs_le (log k)]
      linarith
    have hs0 : 0 < s := by linarith
    have hs3 : s ≤ 3 := by linarith
    have hF : sieveUpper306 s = 2 * exp eulerMascheroniConstant / s :=
      linear_sieve_formulas306.1 s hs0 hs3
    have hFle : sieveUpper306 s ≤ (1 + η) * exp eulerMascheroniConstant := by
      rw [hF, div_le_iff₀ hs0]
      have : 2 ≤ (1 + η) * s := by nlinarith
      nlinarith
    obtain ⟨hh0, hh1⟩ := hSieve_bounds337 s
    have he2 : exp 2 * exp (-2) = 1 := by rw [← exp_add]; norm_num
    have hεh : ε * 106 * exp 2 * LeanLab.ChenExplicit.hSieve s ≤ η * exp eulerMascheroniConstant := by
      have h := mul_le_mul_of_nonneg_left hh1 (show 0 ≤ ε * 106 * exp 2 by positivity)
      have : ε * 106 * exp 2 * exp (-2) = ε * 106 := by rw [mul_assoc, he2, mul_one]
      linarith
    have hφ : upperPhi337 ε s ≤ (1 + η) ^ 2 * exp eulerMascheroniConstant := by
      unfold upperPhi337
      nlinarith [mul_pos hη0 hγ]
    have hφ0 : 0 ≤ upperPhi337 ε s := by
      unfold upperPhi337
      have := sieveUpper_pos306 s hs0
      positivity
    obtain ⟨hV0, _⟩ := sw2V_bounds337 N B he
    have hVb := hV he
    -- the pair sum
    set Sp : ℝ := ∑ b ∈ switchedThreePairs306 N,
      1 / ((b.1 * b.2 : ℕ) * log ((N : ℝ) / (b.1 * b.2 : ℕ))) with hSdef
    have hS0 : 0 ≤ Sp := by
      apply Finset.sum_nonneg
      intro b hb
      have hE : b.1 * b.2 ∈ switchedThreeE306 N := mem_image_of_mem _ hb
      have hr3 := switchedThreeE_range337 N (b.1 * b.2) hN2 hE
      have hbp : (0 : ℝ) < ((b.1 * b.2 : ℕ) : ℝ) := by exact_mod_cast hr3.1
      have hle : ((b.1 * b.2 : ℕ) : ℝ) ≤ N := by
        refine hr3.2.le.trans ?_
        simpa using rpow_le_rpow_of_exponent_le hN1.le (by norm_num : (2 / 3 : ℝ) ≤ 1)
      have hl : 0 ≤ log ((N : ℝ) / (b.1 * b.2 : ℕ)) :=
        log_nonneg ((one_le_div hbp).mpr hle)
      positivity
    have hP2 : sieveThreePairSum337 N = 8 / (2 * (0.95 : ℝ) - 1) * log N * Sp := rfl
    have hP20 : 0 ≤ sieveThreePairSum337 N := by rw [hP2]; positivity
    have hP2a : sieveThreePairSum337 N ≤ Pa := by
      have := hPb N hNP
      linarith [le_abs_self (sieveThreeCoefficient337 + 1)]
    set Xb : ℝ := (1 + η) * ((N : ℝ) ^ (0.95 : ℝ) * Sp) with hXb
    have hXb0 : 0 ≤ Xb := by positivity
    set Vb : ℝ := (1 + η) * (2 * exp (-eulerMascheroniConstant) * C N / (0.225 * log N))
      with hVbdef
    have step1 : upperPhi337 ε s * sw3X337 N * sw2V337 N B ≤ upperPhi337 ε s * Xb * sw2V337 N B := by
      apply mul_le_mul_of_nonneg_right _ hV0.le
      exact mul_le_mul_of_nonneg_left hX hφ0
    have step2 : upperPhi337 ε s * Xb * sw2V337 N B ≤
        ((1 + η) ^ 2 * exp eulerMascheroniConstant) * Xb * Vb := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right hφ hXb0) hVb hV0.le (by positivity)
    have hid : ((1 + η) ^ 2 * exp eulerMascheroniConstant) * Xb * Vb =
        (1 + η) ^ 4 * (sieveThreePairSum337 N * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2)) := by
      rw [hXb, hVbdef, hP2, exp_neg]
      field_simp
      ring
    have hpow : (1 + η) ^ 4 ≤ 1 + 15 * η := by
      have q2 : η ^ 2 ≤ η := by nlinarith
      have q3 : η ^ 3 ≤ η := by
        have : η ^ 3 = η ^ 2 * η := by ring
        nlinarith [pow_pos hη0 2]
      have q4 : η ^ 4 ≤ η := by
        have : η ^ 4 = η ^ 3 * η := by ring
        nlinarith [pow_pos hη0 3]
      have : (1 + η) ^ 4 = 1 + 4 * η + 6 * η ^ 2 + 4 * η ^ 3 + η ^ 4 := by ring
      linarith
    have hK : 0 < C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2 := leaf118_scale_pos N hN2
    have hfin : (1 + η) ^ 4 * sieveThreePairSum337 N ≤ sieveThreePairSum337 N + δ := by
      nlinarith [mul_le_mul_of_nonneg_right hpow hP20, mul_le_mul_of_nonneg_left hP2a hη0.le]
    calc upperPhi337 ε s * sw3X337 N * sw2V337 N B ≤ _ := step1.trans step2
      _ = _ := hid
      _ = ((1 + η) ^ 4 * sieveThreePairSum337 N) * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfin hK.le
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hall
  exact ⟨N0, fun N he hN => hN0 N hN he⟩

#print axioms leaf337_three_main_term

set_option maxHeartbeats 1600000 in
/-- Page 604 display 4.15, its first inequality before prime pair summation.
This is the all large count to weighted pair sum step, by the analogous switching
argument of displays 4.8 to 4.13. Assembled from the finite closed endpoint and small
prime losses, switched_upper_finite306 CONDITIONAL ON the cited leaf306_theorem6, the
remainder split of display 4.10, sieve_three_R2_small337, the cited uniform Wu input
leaf337_three_wu_uniform, and the proved main term leaf337_three_main_term. -/
theorem leaf337_three_switching :
    ∀ δ : ℝ, 0 < δ → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (((switchedClosedIndex337 N (switchedThreeE306 N)).filter
        (fun b => (N - b.1 * b.2).Prime)).card : ℝ) ≤ (sieveThreePairSum337 N + δ) *
        (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
  classical
  intro δ hδ
  obtain ⟨ε, hε, hεmax, hmainε⟩ := leaf337_three_main_term (δ / 4) (by positivity)
  obtain ⟨w, hw, hupper⟩ := switched_upper_finite306 leaf306_theorem6 ε hε hεmax
  obtain ⟨M, hM0, hM⟩ := upper_phi_bound337 ε hε.le
  have hk0 : 0 ≤ ∏ p ∈ oddSievePrimes306 w, (p : ℝ) :=
    Finset.prod_nonneg (fun p _ => Nat.cast_nonneg p)
  set k : ℝ := 1 + ∏ p ∈ oddSievePrimes306 w, (p : ℝ) with hkdef
  have hk : 0 < k := by rw [hkdef]; linarith
  obtain ⟨B, hB, Kw, hKw, nW, hW⟩ := leaf337_three_wu_uniform 4 (by norm_num)
  obtain ⟨nM, hmain⟩ := hmainε B k hB hk
  obtain ⟨C4, hC4, hC4sum⟩ := LeanLab.PNTPort.BV.sum_inv_totient_le
  obtain ⟨nR, hR2⟩ := sieve_three_R2_small337 (δ / 4) (by positivity)
  obtain ⟨nS, hS⟩ := switched_small_value_loss337 (δ / 4) (by positivity)
  have hlogN : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (0.25 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  set H : ℝ := Kw * (1 + M + 2 * C4) with hH
  have htw := LeanLab.ChenExplicit.twinC_pos
  have hall : ∀ᶠ N : ℕ in atTop, Even N →
      (((switchedClosedIndex337 N (switchedThreeE306 N)).filter
        (fun b => (N - b.1 * b.2).Prime)).card : ℝ) ≤ (sieveThreePairSum337 N + δ) *
        (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
    filter_upwards [sw2_level_bounds337 B hB,
      hpow.eventually_ge_atTop (max 2 (max (w ^ 2 + 1) (exp (40 * |log k| + 40)))),
      hlogN.eventually_ge_atTop (max 1 (H / (δ / 4 * LeanLab.ChenExplicit.twinC))),
      eventually_ge_atTop nW, eventually_ge_atTop nM, eventually_ge_atTop nR,
      eventually_ge_atTop nS, eventually_ge_atTop (3 : ℕ)]
      with N hLb hpN hlN hNW hNM hNR hNS hN3
    intro he
    have hN2 : 2 ≤ N := by omega
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hlN1 : 1 ≤ log (N : ℝ) := (le_max_left ..).trans hlN
    have hlNH : H / (δ / 4 * LeanLab.ChenExplicit.twinC) ≤ log (N : ℝ) :=
      (le_max_right ..).trans hlN
    have hK : 0 < C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2 := leaf118_scale_pos N hN2
    set K0 : ℝ := C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2 with hK0
    set L : ℝ := sw2Level337 N B with hLdef
    have hL2 : 2 ≤ L := le_trans (le_max_left ..) (hpN.trans hLb.1)
    have hLw : w ^ 2 + 1 ≤ L := le_trans ((le_max_left ..).trans (le_max_right ..))
      (hpN.trans hLb.1)
    have hLe : exp (40 * |log k| + 40) ≤ L := le_trans ((le_max_right ..).trans
      (le_max_right ..)) (hpN.trans hLb.1)
    have hlogL : 40 * |log k| + 40 ≤ log L := by
      have := log_le_log (exp_pos _) hLe
      rwa [log_exp] at this
    have hlogLp : 0 < log L := by linarith [abs_nonneg (log k)]
    -- the parameter
    have hs := sw2_param_eq337 N B k hk (by linarith)
    have hsr : sw2Param337 N B k ∈ Set.Icc (1.8 : ℝ) 4.3 := by
      rw [hs]
      have h1 : 2 * log k / log L ≤ 0.2 := by
        rw [div_le_iff₀ hlogLp]; linarith [le_abs_self (log k)]
      have h2 : -0.2 ≤ 2 * log k / log L := by
        rw [le_div_iff₀ hlogLp]; linarith [neg_abs_le (log k)]
      constructor <;> linarith
    obtain ⟨hφ0, hφM⟩ := hM _ hsr
    set z : ℝ := sw2Cut337 N B with hzdef
    have hzw : w < z := by
      rw [hzdef, sw2Cut337, ← hLdef]
      apply Real.lt_sqrt (by linarith) |>.mpr
      linarith
    have hz1 : 1 < z := by linarith
    have hDpos : 0 < L / k := div_pos (by linarith) hk
    have hzD : z ≤ L / k := by
      have h1 : 1 ≤ sw2Param337 N B k := by linarith [hsr.1]
      unfold sw2Param337 at h1
      rw [← hzdef, ← hLdef] at h1
      have hlz : 0 < log z := log_pos hz1
      rw [le_div_iff₀ hlz, one_mul] at h1
      exact (log_le_log_iff (by linarith) hDpos).mp h1
    have hz225 : z ≤ (N : ℝ) ^ (0.225 : ℝ) := by
      rw [hzdef, sw2Cut337, ← hLdef]
      calc Real.sqrt L ≤ Real.sqrt ((N : ℝ) ^ (0.45 : ℝ)) := Real.sqrt_le_sqrt hLb.2
        _ = (N : ℝ) ^ (0.225 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← rpow_mul hNp.le]; norm_num
    have hLN : L ≤ N := by
      refine hLb.2.trans ?_
      simpa using rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ N by omega) : (1 : ℝ) ≤ N) (by norm_num : (0.45 : ℝ) ≤ 1)
    have hfl : ⌊L⌋₊ ≤ N := by
      have : (⌊L⌋₊ : ℝ) ≤ N := (Nat.floor_le (by linarith)).trans hLN
      exact_mod_cast this
    have hfl1 : 1 ≤ ⌊L⌋₊ := Nat.le_floor (by norm_num; linarith)
    -- finite losses
    set E := switchedThreeE306 N with hEdef
    set T := switchedIndex306 N E with hTdef
    set PP : ℕ := ∏ p ∈ LeanLab.ChenExplicit.primesBelowIn
      {p : ℕ | p.Prime ∧ p.Coprime N} z, p with hPP
    have h0 := switched_closed_selection337 N hN2 E Nat.Prime
    have h1 := switched_prime_sift337 N hN2 E {p : ℕ | p.Prime ∧ p.Coprime N}
      (fun p hp => hp.1) z
    dsimp only at h1
    have hloss := hS N hNS E (switchedThreeE_card337 N hN2) z hz225
    have hfin : (((switchedClosedIndex337 N E).filter
        (fun b => (N - b.1 * b.2).Prime)).card : ℝ) ≤
        ((T.filter (fun b => (N - b.1 * b.2).Coprime PP)).card : ℝ) +
          (E.card * (⌈z⌉₊ + 1) : ℝ) := by
      have hh : ((switchedClosedIndex337 N E).filter
          (fun b => (N - b.1 * b.2).Prime)).card ≤
          (T.filter (fun b => (N - b.1 * b.2).Coprime PP)).card + E.card * ⌈z⌉₊ + E.card :=
        h0.trans (Nat.add_le_add_right h1 _)
      have hh' : (((switchedClosedIndex337 N E).filter
          (fun b => (N - b.1 * b.2).Prime)).card : ℝ) ≤
          ((T.filter (fun b => (N - b.1 * b.2).Coprime PP)).card : ℝ) +
            (E.card : ℝ) * (⌈z⌉₊ : ℝ) + (E.card : ℝ) := by exact_mod_cast hh
      linarith
    -- Theorem 6
    have h6 := hupper N he E z hzw (L / k) hzD
    dsimp only at h6
    set Qw : Finset ℕ := LeanLab.ChenExplicit.primesBelowIn
      {p : ℕ | p.Prime ∧ p.Coprime N} w with hQw
    set R : ℕ → ℝ := fun d => |(((T.filter (fun b => d ∣ N - b.1 * b.2)).card : ℝ) -
      (T.card : ℝ) * caiDensity118 d)| with hRdef
    change ((T.filter (fun b => (N - b.1 * b.2).Coprime PP)).card : ℝ) ≤
      upperPhi337 ε (sw2Param337 N B k) * (T.card : ℝ) * sw2V337 N B +
        ∑ d ∈ PP.divisors.filter (fun d : ℕ => (d : ℝ) < (∏ p ∈ Qw, (p : ℝ)) * (L / k)), R d
      at h6
    have hQk : (∏ p ∈ Qw, (p : ℝ)) ≤ k := by
      have := sieve_exceptional_product306 w {p : ℕ | p.Prime ∧ p.Coprime N}
        (fun p hp => cai_primes_odd306 N p he hp.1 hp.2)
      rw [hkdef]; linarith
    have hcut : (∏ p ∈ Qw, (p : ℝ)) * (L / k) ≤ L := by
      calc (∏ p ∈ Qw, (p : ℝ)) * (L / k) ≤ k * (L / k) :=
            mul_le_mul_of_nonneg_right hQk hDpos.le
        _ = L := by field_simp
    have hdiv := sieve_divisor_remainder306 N {p : ℕ | p.Prime ∧ p.Coprime N}
      (fun p hp => hp.2) z Qw (L / k) L hcut R (fun _ => abs_nonneg _)
    set U := (Icc 1 ⌊L⌋₊).filter (fun d => N.Coprime d) with hU
    -- remainder pieces
    let nc : ℕ → ℝ := fun d => |∑ e ∈ E.filter (fun e => ¬ e.Coprime d),
      switchedLiTerm337 N e / (d.totient : ℝ)|
    have hwu1 : |(T.card : ℝ) - sw3X337 N| ≤ sw3Wu337 N 1 := by
      have h := switched_remainder_split337 N 1 (Nat.coprime_one_right N) E
      have hT1 : T.filter (fun b => 1 ∣ N - b.1 * b.2) = T :=
        Finset.filter_true_of_mem (fun _ _ => one_dvd _)
      have hE1 : E.filter (fun e => ¬ e.Coprime 1) = ∅ :=
        Finset.filter_false_of_mem (fun e _ => by simp)
      rw [hT1, hE1, Finset.sum_empty, abs_zero, add_zero] at h
      simpa only [sw3Wu337, sw3X337, Nat.totient_one, Nat.cast_one, div_one] using h
    have hRd : ∀ d ∈ U, R d ≤ sw3Wu337 N d + nc d + caiDensity118 d * sw3Wu337 N 1 := by
      intro d hd
      have hc : N.Coprime d := (Finset.mem_filter.mp hd).2
      have h := switched_remainder_split337 N d hc E
      have hg : caiDensity118 d = 1 / (d.totient : ℝ) := rfl
      have hg0 : 0 ≤ caiDensity118 d := by rw [hg]; positivity
      have htri : R d ≤ abs ((((T.filter (fun b => d ∣ N - b.1 * b.2)).card : ℝ) -
          (∑ e ∈ E, switchedLiTerm337 N e) / (d.totient : ℝ))) +
          caiDensity118 d * abs ((T.card : ℝ) - sw3X337 N) := by
        have heq : (((T.filter (fun b => d ∣ N - b.1 * b.2)).card : ℝ) -
            (T.card : ℝ) * caiDensity118 d) =
            ((((T.filter (fun b => d ∣ N - b.1 * b.2)).card : ℝ) -
              (∑ e ∈ E, switchedLiTerm337 N e) / d.totient) +
            caiDensity118 d * (sw3X337 N - (T.card : ℝ))) := by
          rw [hg]; unfold sw3X337; ring
        change abs _ ≤ _
        rw [heq]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hg0, abs_sub_comm (sw3X337 N)]
      have hmul := mul_le_mul_of_nonneg_left hwu1 hg0
      have h' : abs ((((T.filter (fun b => d ∣ N - b.1 * b.2)).card : ℝ) -
          (∑ e ∈ E, switchedLiTerm337 N e) / (d.totient : ℝ))) ≤ sw3Wu337 N d + nc d := h
      linarith
    have hsumR : (∑ d ∈ U, R d) ≤ (∑ d ∈ U, sw3Wu337 N d) + (∑ d ∈ U, nc d) +
        sw3Wu337 N 1 * ∑ d ∈ U, caiDensity118 d := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro d hd
      have := hRd d hd
      linarith
    have hWsum := hW N hNW
    have hnc : (∑ d ∈ U, nc d) ≤ δ / 4 * K0 := by
      refine le_trans ?_ (hR2 N hNR ⌊L⌋₊ hfl)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => abs_nonneg _)
    have hg : (∑ d ∈ U, caiDensity118 d) ≤ C4 * (1 + log N) := by
      have h0 : (∑ d ∈ U, caiDensity118 d) = ∑ d ∈ U, (1 : ℝ) / d.totient := rfl
      have h1 : (∑ d ∈ U, caiDensity118 d) ≤ ∑ d ∈ Icc 1 ⌊L⌋₊, (1 : ℝ) / d.totient := by
        rw [h0]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun d _ _ => by positivity)
      refine h1.trans ((hC4sum ⌊L⌋₊).trans ?_)
      apply mul_le_mul_of_nonneg_left _ hC4.le
      have : log (⌊L⌋₊ : ℝ) ≤ log N :=
        log_le_log (by exact_mod_cast (show 0 < ⌊L⌋₊ by omega)) (by exact_mod_cast hfl)
      linarith
    have hwu1U : sw3Wu337 N 1 ≤ ∑ d ∈ U, sw3Wu337 N d :=
      Finset.single_le_sum (f := fun d => sw3Wu337 N d) (fun _ _ => abs_nonneg _)
        (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hfl1⟩, Nat.coprime_one_right N⟩)
    have hwu10 : 0 ≤ sw3Wu337 N 1 := abs_nonneg _
    -- main term
    obtain ⟨hV0, hV1⟩ := sw2V_bounds337 N B he
    have hmainN := hmain N he hNM
    have hTX : (T.card : ℝ) ≤ sw3X337 N + sw3Wu337 N 1 := by
      linarith [le_abs_self ((T.card : ℝ) - sw3X337 N)]
    have hφV : upperPhi337 ε (sw2Param337 N B k) * sw2V337 N B ≤ M := by nlinarith
    have hmain' : upperPhi337 ε (sw2Param337 N B k) * (T.card : ℝ) * sw2V337 N B ≤
        upperPhi337 ε (sw2Param337 N B k) * sw3X337 N * sw2V337 N B + M * sw3Wu337 N 1 := by
      have h := mul_le_mul_of_nonneg_left hTX (mul_nonneg hφ0 hV0.le)
      nlinarith [mul_le_mul_of_nonneg_right hφV hwu10]
    -- the Wu error total
    set Wsum : ℝ := Kw * (N : ℝ) ^ (0.95 : ℝ) / log N ^ (4 : ℝ) with hWs
    have hWerr : Wsum * (1 + M + C4 * (1 + log N)) ≤ δ / 4 * K0 := by
      have hlp : 0 < log (N : ℝ) := by linarith
      have hW0 : 0 ≤ Wsum := by positivity
      have hfac : 1 + M + C4 * (1 + log N) ≤ (1 + M + 2 * C4) * log N := by nlinarith
      have hHl : H ≤ δ / 4 * LeanLab.ChenExplicit.twinC * log N := by
        have := (div_le_iff₀ (by positivity)).mp hlNH
        linarith
      have hC : LeanLab.ChenExplicit.twinC ≤ C N := by
        unfold C
        exact le_mul_of_one_le_right LeanLab.ChenExplicit.twinC_pos.le
          (LeanLab.ChenExplicit.one_le_oddFactor N)
      calc Wsum * (1 + M + C4 * (1 + log N)) ≤ Wsum * ((1 + M + 2 * C4) * log N) :=
            mul_le_mul_of_nonneg_left hfac hW0
        _ = H * ((N : ℝ) ^ (0.95 : ℝ) / log N ^ 3) := by
            rw [hWs, hH, rpow_ofNat]; field_simp
        _ ≤ (δ / 4 * LeanLab.ChenExplicit.twinC * log N) * ((N : ℝ) ^ (0.95 : ℝ) / log N ^ 3) :=
            mul_le_mul_of_nonneg_right hHl (by positivity)
        _ = δ / 4 * (LeanLab.ChenExplicit.twinC * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
            field_simp
        _ ≤ δ / 4 * K0 := by
            rw [hK0]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply div_le_div_of_nonneg_right _ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_right hC (rpow_pos_of_pos hNp _).le
    have hWsumU : (∑ d ∈ U, sw3Wu337 N d) ≤ Wsum := hWsum
    have hgw : sw3Wu337 N 1 * ∑ d ∈ U, caiDensity118 d ≤ Wsum * (C4 * (1 + log N)) := by
      have hg0 : 0 ≤ ∑ d ∈ U, caiDensity118 d :=
        Finset.sum_nonneg (fun d _ => by
          change 0 ≤ 1 / (d.totient : ℝ); positivity)
      calc sw3Wu337 N 1 * ∑ d ∈ U, caiDensity118 d ≤ Wsum * ∑ d ∈ U, caiDensity118 d :=
            mul_le_mul_of_nonneg_right (hwu1U.trans hWsumU) hg0
        _ ≤ Wsum * (C4 * (1 + log N)) :=
            mul_le_mul_of_nonneg_left hg (by rw [hWs]; positivity)
    have hMw : M * sw3Wu337 N 1 ≤ M * Wsum :=
      mul_le_mul_of_nonneg_left (hwu1U.trans hWsumU) hM0
    have hRem := hdiv.trans hsumR
    rw [← hK0] at hmainN hloss
    have : Wsum * (1 + M + C4 * (1 + log N)) =
        Wsum + M * Wsum + Wsum * (C4 * (1 + log N)) := by ring
    linarith [hfin, h6, hRem, hmain', hmainN, hloss, hnc, hWerr, hgw, hMw, hWsumU]
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hall
  exact ⟨N0, fun N he hN => hN0 N hN he⟩

/-- The exact sealed third upper leaf follows from the two smaller analytic steps.
CONDITIONAL ON leaf337_three_switching and leaf337_three_pair_sum. -/
theorem sieve_three_supply337 :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (S3 N 0.95 : ℝ) ≤
        0.1564 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := by
  obtain ⟨N0, h0⟩ := leaf337_three_switching 0.00001 (by norm_num)
  obtain ⟨N1, h1⟩ := leaf337_three_pair_sum 0.00001 (by norm_num)
  refine ⟨max 2 (max N0 N1), fun N he hN => ?_⟩
  have h2 : 2 ≤ N := (le_max_left ..).trans hN
  have h0N : N0 ≤ N := (le_max_left N0 N1).trans ((le_max_right ..).trans hN)
  have h1N : N1 ≤ N := (le_max_right N0 N1).trans ((le_max_right ..).trans hN)
  apply (Nat.cast_le.mpr (sieve_three_closed337 N h2)).trans
  apply (h0 N he h0N).trans
  apply mul_le_mul_of_nonneg_right _ (leaf118_scale_pos N h2).le
  have hc : sieveThreeCoefficient337 ≤ 0.15635 := eq415_margin118
  have := h1 N h1N
  linarith

#print axioms leaf337_three_switching
#print axioms leaf337_three_pair_sum
#print axioms sieve_three_supply337

end LeanLab.Cai2002

