/-
Cai 2002 page 602 display 4.7. Supply split for the first upper leaf.
The sealed Decomp118 file is unchanged. The two analytic steps remain open.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Decomp118

open Filter Finset Real
open scoped Topology
noncomputable section
namespace LeanLab.Cai2002

/-- The exact coefficient before rounding in page 602 display 4.7. -/
def sieveOneCoefficient337 : ℝ :=
  8 / (0.95 : ℝ) ^ 2 * (log ((11 * 0.95 - 2) / (3.29 * 0.95 - 2)) +
    ∫ s in (2 : ℝ)..(5.5 * 0.95 - 2),
      log (s - 1) / s * log ((5.5 * 0.95 - 1) * (5.5 * 0.95 - 1 - s) / (s + 1)))

/-- The weighted prime sum in the first line of page 602 display 4.7.
Coprimality with N is dropped for an upper bound. The sieve function is global. -/
def sieveOnePrimeSum337 (N : ℕ) : ℝ :=
  22 * exp (-Real.eulerMascheroniConstant) / 0.95 *
    ∑ q ∈ (range (N + 1)).filter (fun q : ℕ =>
      q.Prime ∧ z1 N ≤ (q : ℝ) ∧ (q : ℝ) < z2 N),
      sieveUpper306 (5.5 * 0.95 - 11 * log q / log N) / (q : ℝ)

/-- A strict coefficient reserve absorbs two arbitrarily small additive errors.
Derived from page 602 display 4.7 and the positive scale on page 597. -/
theorem sieve_upper_of_limit337 (a m : ℕ → ℝ) (c k : ℝ) (hck : c < k)
    (hm : Tendsto m atTop (𝓝 c))
    (ha : ∀ δ : ℝ, 0 < δ → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      a N ≤ (m N + δ) * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2)) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      a N ≤ k * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
  let δ := (k - c) / 3
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨N0, hN0⟩ := ha δ hδ
  have hnear : ∀ᶠ N : ℕ in atTop, m N < c + δ :=
    hm.eventually (eventually_lt_nhds (by linarith : c < c + δ))
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hnear
  refine ⟨max 2 (max N0 N1), fun N he hN => ?_⟩
  have h2 : 2 ≤ N := (le_max_left ..).trans hN
  have h0 : N0 ≤ N := (le_max_left N0 N1).trans ((le_max_right ..).trans hN)
  have h1 : N1 ≤ N := (le_max_right N0 N1).trans ((le_max_right ..).trans hN)
  apply (hN0 N he h0).trans
  apply mul_le_mul_of_nonneg_right _ (leaf118_scale_pos N h2).le
  have := hN1 N h1
  dsimp [δ] at *
  linarith

/-- The full sequence remainder centered at its exact prime mass.
Page 601 displays 4.5 to 4.6, in the normalization of cai_remainder_level118. -/
def caiRemainder337 (N d : ℕ) : ℝ :=
  |(((caiSequence118 N).filter (fun a => d ∣ a)).card : ℝ) -
    ((caiSequence118 N).card : ℝ) * caiDensity118 d|

/-- The complete recentering correction costs one logarithm uniformly over the index set.
Page 601 display 4.6. This retains the correction from cai_q_remainder_identity306. -/
theorem sieve_one_recenter_sum337 :
    ∃ K : ℝ, 0 < K ∧ ∀ (N D : ℕ) (z : ℝ) (T : Finset (ℕ × ℕ)),
      (∀ b ∈ T, b.1.Prime ∧ z ≤ (b.1 : ℝ) ∧ 0 < b.2 ∧
        (∀ p ∈ b.2.primeFactors, (p : ℝ) < z) ∧
        b.1 * b.2 ≤ D ∧ N.Coprime (b.1 * b.2)) →
      (∑ b ∈ T,
        |((((caiSequence118 N).filter (fun a => b.1 ∣ a)).filter
            (fun a => b.2 ∣ a)).card : ℝ) -
          (((caiSequence118 N).filter (fun a => b.1 ∣ a)).card : ℝ) * caiDensity118 b.2|) ≤
        (1 + K * (1 + log D)) *
          ∑ m ∈ (Icc 1 D).filter (fun m => N.Coprime m), caiRemainder337 N m := by
  classical
  obtain ⟨K, hK, hden⟩ := LeanLab.PNTPort.BV.sum_inv_totient_le
  refine ⟨K, hK, fun N D z T hT => ?_⟩
  let U := (Icc 1 D).filter (fun m => N.Coprime m)
  have hqd (b : ℕ × ℕ) (hb : b ∈ T) : b.1.Coprime b.2 := by
    obtain ⟨hq, hqz, hd, hdf, _, _⟩ := hT b hb
    apply hq.coprime_iff_not_dvd.mpr
    intro hdiv
    have hh := hdf b.1 (Nat.mem_primeFactors.mpr ⟨hq, hdiv, hd.ne'⟩)
    linarith
  have hfirst : (∑ b ∈ T, caiRemainder337 N (b.1 * b.2)) ≤
      ∑ m ∈ U, caiRemainder337 N m := by
    have hh := sieve_one_remainder_sum118 T z D
      (fun b hb => by
        obtain ⟨hq, hqz, hd, hdf, hbd, _⟩ := hT b hb
        exact ⟨hq, hqz, hd, hdf, hbd⟩)
      (fun m => if N.Coprime m then caiRemainder337 N m else 0)
      (fun m _ => by
        split_ifs
        · exact abs_nonneg _
        · exact le_refl 0)
    have heq : (∑ b ∈ T, if N.Coprime (b.1 * b.2) then
        caiRemainder337 N (b.1 * b.2) else 0) =
        ∑ b ∈ T, caiRemainder337 N (b.1 * b.2) := by
      apply sum_congr rfl
      intro b hb
      rw [ite_eq_left (hT b hb).2.2.2.2.2]
    rw [heq, ← Finset.sum_filter] at hh
    exact hh
  have hsub : T ⊆ U ×ˢ Icc 1 D := by
    intro b hb
    obtain ⟨hq, _, hd, _, hbd, hc⟩ := hT b hb
    have hp : 0 < b.1 * b.2 := Nat.mul_pos hq.pos hd
    have hqle : b.1 ≤ b.1 * b.2 := Nat.le_of_dvd hp (dvd_mul_right _ _)
    have hdle : b.2 ≤ b.1 * b.2 := Nat.le_of_dvd hp (dvd_mul_left _ _)
    exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hq.pos, hqle.trans hbd⟩,
      hc.coprime_dvd_right (dvd_mul_right _ _)⟩, mem_Icc.mpr ⟨hd, hdle.trans hbd⟩⟩
  have hcorrection : (∑ b ∈ T, caiRemainder337 N b.1 * caiDensity118 b.2) ≤
      (∑ m ∈ U, caiRemainder337 N m) * (K * (1 + log D)) := by
    calc
      _ ≤ ∑ b ∈ U ×ˢ Icc 1 D, caiRemainder337 N b.1 * caiDensity118 b.2 :=
        sum_le_sum_of_subset_of_nonneg hsub (fun b _ _ => by
          dsimp [caiRemainder337, caiDensity118]; positivity)
      _ = (∑ m ∈ U, caiRemainder337 N m) * ∑ d ∈ Icc 1 D, caiDensity118 d := by
        simp only [Finset.sum_product, ← Finset.mul_sum, ← Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hden D) (by
        apply Finset.sum_nonneg
        intro m _
        exact abs_nonneg _)
  calc
    _ ≤ ∑ b ∈ T, (caiRemainder337 N (b.1 * b.2) +
        caiRemainder337 N b.1 * caiDensity118 b.2) :=
      sum_le_sum (fun b hb => cai_q_remainder_bound306 N b.1 b.2 (hqd b hb))
    _ = (∑ b ∈ T, caiRemainder337 N (b.1 * b.2)) +
        ∑ b ∈ T, caiRemainder337 N b.1 * caiDensity118 b.2 := sum_add_distrib
    _ ≤ (∑ m ∈ U, caiRemainder337 N m) +
        (∑ m ∈ U, caiRemainder337 N m) * (K * (1 + log D)) :=
      add_le_add hfirst hcorrection
    _ = _ := by ring

#print axioms sieve_one_recenter_sum337

/-- The entire recentered S1 remainder is negligible uniformly in the selected pairs.
Page 601 display 4.6. The actual pi centered BV level absorbs the logarithmic correction.
No weighted prime main term or cited linear sieve is used here. -/
theorem sieve_one_recenter_small337 (η : ℝ) (hη : 0 < η) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      let D : ℕ := ⌊Real.sqrt ((N : ℝ) ^ (0.95 : ℝ)) /
        log ((N : ℝ) ^ (0.95 : ℝ)) ^ B⌋₊
      ∀ (z : ℝ) (T : Finset (ℕ × ℕ)),
        (∀ b ∈ T, b.1.Prime ∧ z ≤ (b.1 : ℝ) ∧ 0 < b.2 ∧
          (∀ p ∈ b.2.primeFactors, (p : ℝ) < z) ∧
          b.1 * b.2 ≤ D ∧ N.Coprime (b.1 * b.2)) →
        (∑ b ∈ T,
          |((((caiSequence118 N).filter (fun a => b.1 ∣ a)).filter
              (fun a => b.2 ∣ a)).card : ℝ) -
            (((caiSequence118 N).filter (fun a => b.1 ∣ a)).card : ℝ) * caiDensity118 b.2|) ≤
          η * (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
  classical
  obtain ⟨Kr, hKr, hrec⟩ := sieve_one_recenter_sum337
  obtain ⟨B, hB, Kv, hKv, hbv⟩ := cai_remainder_level118 4 (by norm_num)
  let H : ℝ := (1 + 2 * Kr) * Kv / (0.95 : ℝ) ^ 4
  have hH : 0 < H := by dsimp [H]; positivity
  have hηC : 0 < η * LeanLab.ChenExplicit.twinC :=
    mul_pos hη LeanLab.ChenExplicit.twinC_pos
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp
    (hlog.eventually_ge_atTop (max 2 (H / (η * LeanLab.ChenExplicit.twinC))))
  refine ⟨B, hB, max 4 n0, fun N hN => ?_⟩
  dsimp only
  intro z T hT
  have hN4 : 4 ≤ N := (le_max_left ..).trans hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL2 : 2 ≤ log (N : ℝ) :=
    (le_max_left ..).trans (hn0 N ((le_max_right ..).trans hN))
  have hLH : H / (η * LeanLab.ChenExplicit.twinC) ≤ log (N : ℝ) :=
    (le_max_right ..).trans (hn0 N ((le_max_right ..).trans hN))
  have hLp : 0 < log (N : ℝ) := by linarith
  let D : ℕ := ⌊Real.sqrt ((N : ℝ) ^ (0.95 : ℝ)) /
    log ((N : ℝ) ^ (0.95 : ℝ)) ^ B⌋₊
  have hDcast : (D : ℝ) ≤ N := by
    have hx1 : 1 ≤ (N : ℝ) ^ (0.95 : ℝ) :=
      one_le_rpow (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
    have hxN : (N : ℝ) ^ (0.95 : ℝ) ≤ N := by
      simpa using rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num : (0.95 : ℝ) ≤ 1)
    have hden1 : 1 ≤ log ((N : ℝ) ^ (0.95 : ℝ)) ^ B := by
      apply one_le_rpow _ hB.le
      rw [log_rpow hNp]
      nlinarith
    exact (Nat.floor_le (by positivity)).trans
      ((div_le_self (sqrt_nonneg _) hden1).trans
        ((sqrt_le_self_iff.mpr (Or.inr hx1)).trans hxN))
  have hlogD : log (D : ℝ) ≤ log (N : ℝ) := by
    by_cases hD0 : D = 0
    · simp only [hD0, Nat.cast_zero, log_zero]
      linarith
    · exact log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hD0) hDcast
  have hcoef : 1 + Kr * (1 + log D) ≤ (1 + 2 * Kr) * log N := by
    nlinarith [mul_nonneg hKr.le (sub_nonneg.mpr hlogD)]
  have hcoef0 : 0 ≤ 1 + Kr * (1 + log D) := by positivity
  have hsmall : H / log (N : ℝ) ≤ η * LeanLab.ChenExplicit.twinC := by
    apply (div_le_iff₀ hLp).mpr
    have hh := (div_le_iff₀ hηC).mp hLH
    linarith
  have hC : LeanLab.ChenExplicit.twinC ≤ C N := by
    unfold C
    exact le_mul_of_one_le_right LeanLab.ChenExplicit.twinC_pos.le
      (LeanLab.ChenExplicit.one_le_oddFactor N)
  have h0 := hrec N D z T hT
  have h1 : (∑ m ∈ (Icc 1 D).filter (fun m => N.Coprime m), caiRemainder337 N m) ≤
      Kv * (N : ℝ) ^ (0.95 : ℝ) / log ((N : ℝ) ^ (0.95 : ℝ)) ^ (4 : ℝ) := hbv N hN4
  apply h0.trans
  calc
    _ ≤ (1 + Kr * (1 + log D)) *
        (Kv * (N : ℝ) ^ (0.95 : ℝ) / log ((N : ℝ) ^ (0.95 : ℝ)) ^ (4 : ℝ)) :=
      mul_le_mul_of_nonneg_left h1 hcoef0
    _ ≤ ((1 + 2 * Kr) * log N) *
        (Kv * (N : ℝ) ^ (0.95 : ℝ) / log ((N : ℝ) ^ (0.95 : ℝ)) ^ (4 : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoef (by rw [log_rpow hNp]; positivity)
    _ = (H / log (N : ℝ)) * ((N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
      rw [log_rpow hNp, rpow_ofNat, mul_pow]
      dsimp [H]
      field_simp
      <;> ring
    _ ≤ (η * LeanLab.ChenExplicit.twinC) *
        ((N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = η * (LeanLab.ChenExplicit.twinC * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hη.le
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_right hC (rpow_pos_of_pos hNp _).le

#print axioms sieve_one_recenter_small337

/-- Reciprocal prime sums over any fixed positive power block have the expected limit.
Derived block input for prime partial summation in page 602 display 4.7.
This uses the proved elementary Mertens block estimate, not a cited PNT hypothesis. -/
theorem prime_reciprocal_block_limit337 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Tendsto (fun N : ℕ =>
      ∑ p ∈ (Ioc ⌊(N : ℝ) ^ a⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime,
        (1 : ℝ) / p) atTop (𝓝 (log (b / a))) := by
  have hb : 0 < b := ha.trans hab
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have herr : Tendsto (fun N : ℕ => 4 / (a * log (N : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Filter.Tendsto.const_mul_atTop ha hlog)
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [eventually_ge_atTop (2 : ℕ), hpow.eventually_ge_atTop 2,
    herr.eventually (gt_mem_nhds hε)] with N hN hy hsmall
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL0 : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hxy : (N : ℝ) ^ a ≤ (N : ℝ) ^ b :=
    rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) hab.le
  have hh := LeanLab.AlmostPrimes.Decomp1528b.mertens2_block hy hxy
  have hmain : log (log ((N : ℝ) ^ b)) - log (log ((N : ℝ) ^ a)) =
      log (b / a) := by
    rw [log_rpow hN0, log_rpow hN0,
      log_mul hb.ne' hL0.ne', log_mul ha.ne' hL0.ne', log_div hb.ne' ha.ne']
    ring
  rw [hmain, log_rpow hN0] at hh
  rw [Real.dist_eq]
  exact hh.trans_lt hsmall

#print axioms prime_reciprocal_block_limit337

/-- The q dependent sieve parameter differs from its limiting argument by one common shift.
Page 601 display 4.5. A fixed positive factor k permits the exceptional product reduction. -/
theorem upper_q_parameter_identity337 (N q : ℕ) (hN : 2 ≤ N) (hq : 0 < q)
    (B k : ℝ) (hk : 0 < k) :
    log (((N : ℝ) ^ (0.95 / 2 : ℝ) / log N ^ B) / (k * q)) / log (z1 N) =
      5.225 - 11 * log q / log N -
        (11 * B * (log (log N) / log N) + (11 * log k) / log N) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hLp : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [log_div (div_pos (rpow_pos_of_pos hNp _) (rpow_pos_of_pos hLp _)).ne'
    (mul_pos hk hqp).ne', log_div (rpow_pos_of_pos hNp _).ne' (rpow_pos_of_pos hLp _).ne',
    log_rpow hNp, log_rpow hLp, log_mul hk.ne' hqp.ne']
  unfold z1
  rw [log_rpow hNp]
  field_simp
  <;> ring

/-- The varying upper sieve function converges uniformly to its q dependent limiting value.
Pages 601 to 602 displays 4.5 to 4.7. The full prime range is retained. -/
theorem upper_q_parameter_uniform337 (B k : ℝ) (hk : 0 < k) (η : ℝ) (hη : 0 < η) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ q ∈ Q1 N,
      |sieveUpper306 (log (((N : ℝ) ^ (0.95 / 2 : ℝ) / log N ^ B) / (k * q)) / log (z1 N)) -
        sieveUpper306 (5.225 - 11 * log q / log N)| ≤ η := by
  have hF : ContinuousOn sieveUpper306 (Set.Icc (1.8 : ℝ) 4.3) :=
    sieveFns306.2.1.mono (by intro s hs; change 0 < s; linarith [hs.1])
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hF) η hη
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun N : ℕ => log (log (N : ℝ)) / log N) atTop (𝓝 0) :=
    isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  have hshift : Tendsto (fun N : ℕ =>
      11 * B * (log (log (N : ℝ)) / log N) + (11 * log k) / log N) atTop (𝓝 0) := by
    simpa using (hsmall.const_mul (11 * B)).add (tendsto_const_nhds.div_atTop hlog)
  have hrad : 0 < min δ (0.05 : ℝ) := lt_min hδ (by norm_num)
  have hnear := hshift.eventually (Metric.ball_mem_nhds (0 : ℝ) hrad)
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero] at hnear
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp hnear
  refine ⟨max 2 n0, fun N hN q hq => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left ..).trans hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLp : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  obtain ⟨_, hprime, hqlo, hqhi, _⟩ :=
    (show q < N + 1 ∧ q.Prime ∧ z1 N ≤ (q : ℝ) ∧ (q : ℝ) < z2 N ∧ q.Coprime N from by
      simpa only [Q1, mem_filter, mem_range] using hq)
  have hqp : (0 : ℝ) < q := by exact_mod_cast hprime.pos
  have hlo : (1 / 11 : ℝ) ≤ log q / log N := by
    have hh := log_le_log (rpow_pos_of_pos hNp (1 / 11 : ℝ)) hqlo
    rw [log_rpow hNp] at hh
    apply (le_div_iff₀ hLp).mpr
    linarith
  have hhi : log q / log N ≤ (1 / 3.29 : ℝ) := by
    have hh := log_lt_log hqp hqhi
    unfold z2 at hh
    rw [log_rpow hNp] at hh
    apply (div_le_iff₀ hLp).mpr
    linarith
  let t : ℝ := 5.225 - 11 * log q / log N
  let v : ℝ := 11 * B * (log (log (N : ℝ)) / log N) + (11 * log k) / log N
  have hv : |v| < min δ 0.05 := hn0 N ((le_max_right ..).trans hN)
  have ht : t ∈ Set.Icc (1.8 : ℝ) 4.3 := by
    dsimp [t]
    simp only [mul_div_assoc]
    constructor <;> linarith
  have htv : t - v ∈ Set.Icc (1.8 : ℝ) 4.3 := by
    have hvsmall : |v| < 0.05 := hv.trans_le (min_le_right ..)
    have hvbounds := abs_lt.mp hvsmall
    dsimp [t]
    simp only [mul_div_assoc]
    constructor <;> linarith
  rw [upper_q_parameter_identity337 N q hN2 hprime.pos B k hk]
  have hh := hmod (t - v) htv t ht (by
    rw [Real.dist_eq, show t - v - t = -v by ring, abs_neg]
    exact hv.trans_le (min_le_left ..))
  exact (show |sieveUpper306 (t - v) - sieveUpper306 t| < η from hh).le

#print axioms upper_q_parameter_identity337
#print axioms upper_q_parameter_uniform337

/-! ### The two branches of the constructed upper sieve function -/

private theorem F_small337 (u : ℝ) (h0 : 0 < u) (h3 : u ≤ 3) :
    sieveUpper306 u = 2 * exp eulerMascheroniConstant / u :=
  linear_sieve_formulas306.1 u h0 h3

private theorem F_large337 (u : ℝ) (h3 : 3 ≤ u) (h5 : u ≤ 5) :
    sieveUpper306 u = 2 * exp eulerMascheroniConstant / u *
      (1 + ∫ t in (2 : ℝ)..(u - 1), log (t - 1) / t) :=
  linear_sieve_formulas306.2.1 u ⟨h3, h5⟩

/-! ### The weight function `Φ u = log u - log (5.225 - u)` and its derivative -/

private theorem hasDerivAt_phi_gen337 (c u : ℝ) (h0 : 0 < u) (hc : u < c) :
    HasDerivAt (fun v : ℝ => log v - log (c - v)) (1 / u + 1 / (c - u)) u := by
  have hc0 : (c - u) ≠ 0 := by intro h; linarith
  have h1 : HasDerivAt (fun v : ℝ => c - v) (-1) u := by
    simpa using (hasDerivAt_id u).const_sub c
  have h2 : HasDerivAt (fun v : ℝ => log (c - v)) (-(1 / (c - u))) u := by
    have hh := (hasDerivAt_log hc0).comp u h1
    simp only [Function.comp_def] at hh
    simpa [one_div] using hh
  have h3 : HasDerivAt (fun v : ℝ => log v) (1 / u) u := by
    simpa [one_div] using hasDerivAt_log h0.ne'
  have hsub := h3.sub h2
  convert hsub using 1
  ring

private theorem hasDerivAt_phi337 (u : ℝ) (h0 : 0 < u) (hc : u < 5.225) :
    HasDerivAt (fun v : ℝ => log v - log (5.225 - v)) (1 / u + 1 / (5.225 - u)) u :=
  hasDerivAt_phi_gen337 5.225 u h0 hc

/-! ### The inner logarithmic integral `K u = ∫ t in 2..(u-1), log (t-1)/t` -/

private theorem contOn_K_integrand337 :
    ContinuousOn (fun t : ℝ => log (t - 1) / t) (Set.Ioi (1 : ℝ)) := by
  apply ContinuousOn.div
  · apply continuousOn_of_forall_continuousAt
    intro t ht
    simp only [Set.mem_Ioi] at ht
    exact (Real.continuousAt_log (by intro h; linarith)).comp (by fun_prop)
  · fun_prop
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    intro h
    linarith

private theorem intervalIntegrable_K_integrand337 (b : ℝ) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ => log (t - 1) / t) MeasureTheory.volume 2 b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_of_forall_continuousAt
  intro t ht
  have hmin : (2 : ℝ) ≤ min 2 b := le_min le_rfl hb
  have h2 : (2 : ℝ) ≤ t := le_trans hmin ht.1
  apply ContinuousAt.div
  · exact (Real.continuousAt_log (by intro h; linarith)).comp (by fun_prop)
  · fun_prop
  · intro h; linarith

private theorem hasDerivAt_K337 (u : ℝ) (h3 : 3 ≤ u) :
    HasDerivAt (fun v : ℝ => ∫ t in (2 : ℝ)..(v - 1), log (t - 1) / t)
      (log (u - 2) / (u - 1)) u := by
  have hu1 : (2 : ℝ) ≤ u - 1 := by linarith
  have hcont : ContinuousAt (fun t : ℝ => log (t - 1) / t) (u - 1) := by
    apply ContinuousAt.div
    · have hinner : ContinuousAt (fun t : ℝ => t - 1) (u - 1) := by fun_prop
      exact hinner.log (by show u - 1 - 1 ≠ 0; intro h; linarith)
    · fun_prop
    · intro h; linarith
  have hmeas : StronglyMeasurableAtFilter (fun t : ℝ => log (t - 1) / t)
      (𝓝 (u - 1)) MeasureTheory.volume :=
    contOn_K_integrand337.stronglyMeasurableAtFilter isOpen_Ioi (u - 1) (by
      show (1 : ℝ) < u - 1
      linarith)
  have hd := intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_K_integrand337 (u - 1) hu1) hmeas hcont
  have hderiv := hd.comp u ((hasDerivAt_id u).sub_const 1)
  have hval : log (u - 1 - 1) / (u - 1) * 1 = log (u - 2) / (u - 1) := by
    rw [mul_one, show u - 1 - 1 = u - 2 by ring]
  rw [hval] at hderiv
  simpa only [Function.comp_def, id_eq] using hderiv

/-! ### Antiderivatives on `[lo, 4.225]` -/

private theorem integral_phi_deriv337 (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 5.225) :
    ∫ u in a..b, (1 / u + 1 / (5.225 - u)) =
      (log b - log (5.225 - b)) - (log a - log (5.225 - a)) := by
  have hcont : ContinuousOn (fun v : ℝ => log v - log (5.225 - v)) (Set.Icc a b) := by
    apply ContinuousOn.sub
    · apply continuousOn_of_forall_continuousAt
      intro u hu
      exact Real.continuousAt_log (by linarith [hu.1])
    · apply continuousOn_of_forall_continuousAt
      intro u hu
      exact (Real.continuousAt_log (by intro h; linarith [hu.2, hb])).comp (by fun_prop)
  have hderiv : ∀ u ∈ Set.Ioo a b,
      HasDerivAt (fun v : ℝ => log v - log (5.225 - v)) (1 / u + 1 / (5.225 - u)) u := by
    intro u hu
    exact hasDerivAt_phi337 u (lt_trans ha hu.1) (lt_trans hu.2 hb)
  have hint : IntervalIntegrable (fun u : ℝ => 1 / u + 1 / (5.225 - u)) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le ha (le_trans (le_min le_rfl hab) hu.1)
    have huc : u < 5.225 := lt_of_le_of_lt (by simpa [max_eq_right hab] using hu.2) hb
    apply ContinuousAt.add
    · exact continuousAt_const.div continuousAt_id hu0.ne'
    · exact continuousAt_const.div (by fun_prop) (by intro h; linarith)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint

private theorem integral_one_div_mul_sub337 (c a b : ℝ) (hc : 0 < c)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < c) :
    ∫ u in a..b, 1 / (u * (c - u)) =
      (1 / c) * (log b - log (c - b) - (log a - log (c - a))) := by
  have hcont : ContinuousOn (fun v : ℝ => (1 / c) * (log v - log (c - v))) (Set.Icc a b) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.sub
    · apply continuousOn_of_forall_continuousAt
      intro u hu
      exact Real.continuousAt_log (by linarith [hu.1])
    · apply continuousOn_of_forall_continuousAt
      intro u hu
      exact (Real.continuousAt_log (by intro h; linarith [hu.2, hb])).comp (by fun_prop)
  have hderiv : ∀ u ∈ Set.Ioo a b,
      HasDerivAt (fun v : ℝ => (1 / c) * (log v - log (c - v))) (1 / (u * (c - u))) u := by
    intro u hu
    have hu0 : 0 < u := lt_trans ha hu.1
    have huc : u < c := lt_trans hu.2 hb
    have h := (hasDerivAt_phi_gen337 c u hu0 huc).const_mul (1 / c)
    convert h using 1
    field_simp
    ring
  have hint : IntervalIntegrable (fun u : ℝ => 1 / (u * (c - u))) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le ha (le_trans (le_min le_rfl hab) hu.1)
    have huc : u < c := lt_of_le_of_lt (by simpa [max_eq_right hab] using hu.2) hb
    apply ContinuousAt.div continuousAt_const
    · fun_prop
    · intro h
      rcases mul_eq_zero.mp h with h' | h'
      · linarith
      · linarith
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint
  rw [this]
  ring

/-! ### Splitting the coefficient integral at `u = 3` -/

private theorem integrable_F_div337 (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 5.225) :
    IntervalIntegrable (fun u : ℝ => sieveUpper306 u / (5.225 - u)) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_of_forall_continuousAt
  intro u hu
  have hu0 : 0 < u := lt_of_lt_of_le ha (le_trans (le_min le_rfl hab) hu.1)
  have huc : u < 5.225 := lt_of_le_of_lt (by simpa [max_eq_right hab] using hu.2) hb
  exact (sieveFns306.2.1).continuousAt (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hu0)) |>.div
    (by fun_prop) (by intro h; linarith)

private theorem integrable_one_div_add337 (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 5.225) :
    IntervalIntegrable (fun u : ℝ => 1 / u + 1 / (5.225 - u)) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_of_forall_continuousAt
  intro u hu
  have hu0 : 0 < u := lt_of_lt_of_le ha (le_trans (le_min le_rfl hab) hu.1)
  have huc : u < 5.225 := lt_of_le_of_lt (by simpa [max_eq_right hab] using hu.2) hb
  exact (continuousAt_const.div continuousAt_id hu0.ne').add
    (continuousAt_const.div (by fun_prop) (by intro h; linarith))

private theorem integrable_K_mul337 :
    IntervalIntegrable (fun u : ℝ => (∫ t in (2 : ℝ)..(u - 1), log (t - 1) / t) *
      (1 / u + 1 / (5.225 - u))) MeasureTheory.volume 3 4.225 := by
  have h3hi : (3 : ℝ) ≤ 4.225 := by norm_num
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.mul
  · apply continuousOn_of_forall_continuousAt
    intro u hu
    obtain ⟨h1, -⟩ := hu
    have hu3 : (3 : ℝ) ≤ u := le_trans (le_min le_rfl h3hi) h1
    exact (hasDerivAt_K337 u hu3).continuousAt
  · apply continuousOn_of_forall_continuousAt
    intro u hu
    obtain ⟨h1, h2⟩ := hu
    have hu3 : (3 : ℝ) ≤ u := le_trans (le_min le_rfl h3hi) h1
    have hu4 : u ≤ 4.225 := le_trans h2 (le_of_eq (max_eq_right h3hi))
    exact (continuousAt_const.div continuousAt_id (by show u ≠ 0; linarith)).add
      (continuousAt_const.div (by fun_prop) (by show 5.225 - u ≠ 0; intro h; linarith))

private theorem integral_F_split337 :
    ∫ u in (5.225 - 11 * (1 / 3.29))..(4.225), sieveUpper306 u / (5.225 - u) =
      (2 * exp eulerMascheroniConstant / 5.225) *
        (((log 4.225 - log (5.225 - 4.225)) -
          (log (5.225 - 11 * (1 / 3.29)) -
            log (5.225 - (5.225 - 11 * (1 / 3.29))))) +
        ∫ u in (3 : ℝ)..(4.225), (∫ t in (2 : ℝ)..(u - 1), log (t - 1) / t) *
          (1 / u + 1 / (5.225 - u))) := by
  have hlo0 : (0 : ℝ) < 5.225 - 11 * (1 / 3.29) := by norm_num
  have hlo3 : 5.225 - 11 * (1 / 3.29) ≤ (3 : ℝ) := by
    have h : (5.225 : ℝ) - 11 * (1 / 3.29) = 24761 / 13160 := by norm_num
    rw [h]; norm_num
  have h3hi : (3 : ℝ) ≤ 4.225 := by norm_num
  have hhi5 : (4.225 : ℝ) < 5.225 := by norm_num
  have hlow : ∀ u ∈ Set.uIcc (5.225 - 11 * (1 / 3.29)) (3 : ℝ),
      sieveUpper306 u / (5.225 - u) =
        (2 * exp eulerMascheroniConstant / 5.225) * (1 / u + 1 / (5.225 - u)) := by
    intro u hu
    obtain ⟨h1, h2⟩ := hu
    have hu0 : 0 < u := lt_of_lt_of_le hlo0 (le_trans (le_min le_rfl hlo3) h1)
    have hu3 : u ≤ 3 := le_trans h2 (le_of_eq (max_eq_right hlo3))
    have hne : (5.225 - u) ≠ 0 := by intro h; linarith
    rw [F_small337 u hu0 hu3]
    field_simp
    ring
  have hhigh : ∀ u ∈ Set.uIcc (3 : ℝ) (4.225),
      sieveUpper306 u / (5.225 - u) =
        (2 * exp eulerMascheroniConstant / 5.225) *
          ((1 + ∫ t in (2 : ℝ)..(u - 1), log (t - 1) / t) * (1 / u + 1 / (5.225 - u))) := by
    intro u hu
    obtain ⟨h1, h2⟩ := hu
    have hu3 : 3 ≤ u := le_trans (le_min le_rfl h3hi) h1
    have hu5 : u ≤ 5 := le_trans (le_trans h2 (le_of_eq (max_eq_right h3hi))) (by norm_num)
    have hne : (5.225 - u) ≠ 0 := by intro h; linarith
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le (by norm_num) hu3
    rw [F_large337 u hu3 hu5]
    field_simp
    ring
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (integrable_F_div337 (5.225 - 11 * (1 / 3.29)) 3 hlo0 hlo3 (by norm_num))
    (integrable_F_div337 3 4.225 (by norm_num) h3hi hhi5)
  rw [← hsplit, intervalIntegral.integral_congr hlow, intervalIntegral.integral_congr hhigh]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hKr : (fun u : ℝ => (1 + ∫ t in (2 : ℝ)..(u - 1), log (t - 1) / t) *
        (1 / u + 1 / (5.225 - u)))
      = fun u : ℝ => (1 / u + 1 / (5.225 - u)) +
        (∫ t in (2 : ℝ)..(u - 1), log (t - 1) / t) * (1 / u + 1 / (5.225 - u)) := by
    funext u; ring
  rw [hKr, intervalIntegral.integral_add
    (integrable_one_div_add337 3 4.225 (by norm_num) h3hi hhi5) integrable_K_mul337]
  have hAdj := intervalIntegral.integral_add_adjacent_intervals
    (integrable_one_div_add337 (5.225 - 11 * (1 / 3.29)) 3 hlo0 hlo3 (by norm_num))
    (integrable_one_div_add337 3 4.225 (by norm_num) h3hi hhi5)
  have hPhi := integral_phi_deriv337 (5.225 - 11 * (1 / 3.29)) 4.225 hlo0 (by linarith) hhi5
  rw [← mul_add, ← add_assoc, hAdj, hPhi]

/-! ### Integration by parts on `[3, 4.225]` -/

private theorem integral_K_by_parts337 :
    ∫ u in (3 : ℝ)..(4.225), (∫ t in (2 : ℝ)..(u - 1), log (t - 1) / t) *
        (1 / u + 1 / (5.225 - u)) =
      (∫ t in (2 : ℝ)..(4.225 - 1), log (t - 1) / t) *
          (log 4.225 - log (5.225 - 4.225)) -
        ∫ u in (3 : ℝ)..(4.225), (log (u - 2) / (u - 1)) * (log u - log (5.225 - u)) := by
  have h3hi : (3 : ℝ) ≤ 4.225 := by norm_num
  have hcont_K : ContinuousOn (fun u : ℝ => ∫ t in (2 : ℝ)..(u - 1), log (t - 1) / t)
      (Set.uIcc (3 : ℝ) 4.225) := by
    apply continuousOn_of_forall_continuousAt
    intro u hu
    obtain ⟨h1, -⟩ := hu
    have hu3 : (3 : ℝ) ≤ u := le_trans (le_min le_rfl h3hi) h1
    exact (hasDerivAt_K337 u hu3).continuousAt
  have hcont_phi : ContinuousOn (fun u : ℝ => log u - log (5.225 - u))
      (Set.uIcc (3 : ℝ) 4.225) := by
    apply ContinuousOn.sub
    · apply continuousOn_of_forall_continuousAt
      intro u hu
      obtain ⟨h1, -⟩ := hu
      have hu3 : (3 : ℝ) ≤ u := le_trans (le_min le_rfl h3hi) h1
      exact Real.continuousAt_log (by linarith)
    · apply continuousOn_of_forall_continuousAt
      intro u hu
      obtain ⟨-, h2⟩ := hu
      have hu4 : u ≤ 4.225 := le_trans h2 (le_of_eq (max_eq_right h3hi))
      have hinner : ContinuousAt (fun v : ℝ => 5.225 - v) u := by fun_prop
      exact hinner.log (by show 5.225 - u ≠ 0; intro h; linarith)
  have hderiv_K : ∀ u ∈ Set.Ioo (min (3 : ℝ) 4.225) (max (3 : ℝ) 4.225),
      HasDerivAt (fun u : ℝ => ∫ t in (2 : ℝ)..(u - 1), log (t - 1) / t)
        (log (u - 2) / (u - 1)) u := by
    intro u hu
    rw [min_eq_left h3hi, max_eq_right h3hi] at hu
    exact hasDerivAt_K337 u (le_of_lt hu.1)
  have hderiv_phi : ∀ u ∈ Set.Ioo (min (3 : ℝ) 4.225) (max (3 : ℝ) 4.225),
      HasDerivAt (fun u : ℝ => log u - log (5.225 - u)) (1 / u + 1 / (5.225 - u)) u := by
    intro u hu
    rw [min_eq_left h3hi, max_eq_right h3hi] at hu
    exact hasDerivAt_phi337 u (by linarith [hu.1]) (by linarith [hu.2])
  have hint_K' : IntervalIntegrable (fun u : ℝ => log (u - 2) / (u - 1)) MeasureTheory.volume 3 4.225 := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro u hu
    obtain ⟨h1, -⟩ := hu
    have hu3 : (3 : ℝ) ≤ u := le_trans (le_min le_rfl h3hi) h1
    apply ContinuousAt.div
    · have hinner : ContinuousAt (fun v : ℝ => v - 2) u := by fun_prop
      exact hinner.log (by show u - 2 ≠ 0; intro h; linarith)
    · fun_prop
    · intro h; linarith
  have hmain := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hcont_K hcont_phi hderiv_K hderiv_phi hint_K'
    (integrable_one_div_add337 3 4.225 (by norm_num) h3hi (by norm_num))
  rw [hmain]
  have hK3 : (∫ t in (2 : ℝ)..(3 - 1), log (t - 1) / t) = 0 := by
    norm_num
  rw [hK3, zero_mul, sub_zero]

private theorem integral_Kprime_phi337 :
    ∫ u in (3 : ℝ)..(4.225), (log (u - 2) / (u - 1)) * (log u - log (5.225 - u)) =
      ∫ t in (2 : ℝ)..(4.225 - 1),
        log (t - 1) / t * (log (t + 1) - log (5.225 - (t + 1))) := by
  have h := intervalIntegral.integral_comp_add_right (a := (2 : ℝ)) (b := 4.225 - 1)
    (f := fun u : ℝ => log (u - 2) / (u - 1) * (log u - log (5.225 - u))) 1
  have h2 : (∫ x in (2 : ℝ)..(4.225 - 1),
      log (x + 1 - 2) / (x + 1 - 1) * (log (x + 1) - log (5.225 - (x + 1)))) =
      ∫ x in (3 : ℝ)..(4.225), log (x - 2) / (x - 1) * (log x - log (5.225 - x)) := by
    rw [h]; norm_num
  rw [← h2]
  apply intervalIntegral.integral_congr
  intro t ht
  simp only
  rw [show t + 1 - 2 = t - 1 by ring, show t + 1 - 1 = t by ring]

private theorem integral_paper_split337 :
    ∫ s in (2 : ℝ)..(4.225 - 1), log (s - 1) / s * log (4.225 * (4.225 - s) / (s + 1)) =
      (∫ t in (2 : ℝ)..(4.225 - 1), log (t - 1) / t) * log 4.225 -
        ∫ t in (2 : ℝ)..(4.225 - 1), log (t - 1) / t * (log (t + 1) - log (4.225 - t)) := by
  have hb : (2 : ℝ) ≤ 4.225 - 1 := by norm_num
  have hpt : ∀ s ∈ Set.uIcc (2 : ℝ) (4.225 - 1),
      log (4.225 * (4.225 - s) / (s + 1)) = log 4.225 + (log (4.225 - s) - log (s + 1)) := by
    intro s hs
    obtain ⟨h1, h2⟩ := hs
    have h1' : (2 : ℝ) ≤ s := le_trans (le_min le_rfl hb) h1
    have h2' : s ≤ 4.225 - 1 := le_trans h2 (le_of_eq (max_eq_right hb))
    have hs1 : (0 : ℝ) < s + 1 := by linarith
    have hs2 : (0 : ℝ) < 4.225 - s := by linarith
    rw [log_div (by positivity) hs1.ne', log_mul (by norm_num) hs2.ne']
    ring
  have hInt1 : IntervalIntegrable (fun t : ℝ => log (t - 1) / t) MeasureTheory.volume 2 (4.225 - 1) :=
    intervalIntegrable_K_integrand337 (4.225 - 1) hb
  have hcont : ContinuousOn (fun s : ℝ => log (s - 1) / s) (Set.uIcc (2 : ℝ) (4.225 - 1)) := by
    apply continuousOn_of_forall_continuousAt
    intro s hs
    obtain ⟨h1, h2⟩ := hs
    have h1' : (2 : ℝ) ≤ s := le_trans (le_min le_rfl hb) h1
    apply ContinuousAt.div
    · have hi : ContinuousAt (fun v : ℝ => v - 1) s := by fun_prop
      exact hi.log (by show s - 1 ≠ 0; intro h; linarith)
    · fun_prop
    · intro h; linarith
  have hInt2 : IntervalIntegrable (fun s : ℝ => log (s - 1) / s *
      (log (4.225 - s) - log (s + 1))) MeasureTheory.volume 2 (4.225 - 1) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul hcont
    apply ContinuousOn.sub
    · apply continuousOn_of_forall_continuousAt
      intro s hs
      obtain ⟨h1, h2⟩ := hs
      have h2' : s ≤ 4.225 - 1 := le_trans h2 (le_of_eq (max_eq_right hb))
      have hi : ContinuousAt (fun v : ℝ => 4.225 - v) s := by fun_prop
      exact hi.log (by show 4.225 - s ≠ 0; intro h; linarith)
    · apply continuousOn_of_forall_continuousAt
      intro s hs
      obtain ⟨h1, h2⟩ := hs
      have h1' : (2 : ℝ) ≤ s := le_trans (le_min le_rfl hb) h1
      have hi : ContinuousAt (fun v : ℝ => v + 1) s := by fun_prop
      exact hi.log (by show s + 1 ≠ 0; intro h; linarith)
  have hpt' : ∀ s ∈ Set.uIcc (2 : ℝ) (4.225 - 1),
      log (s - 1) / s * log (4.225 * (4.225 - s) / (s + 1)) =
        log (s - 1) / s * (log 4.225 + (log (4.225 - s) - log (s + 1))) := by
    intro s hs; rw [hpt s hs]
  rw [intervalIntegral.integral_congr hpt']
  have hpt2 : ∀ s ∈ Set.uIcc (2 : ℝ) (4.225 - 1),
      log (s - 1) / s * (log 4.225 + (log (4.225 - s) - log (s + 1))) =
        log (s - 1) / s * log 4.225 +
          log (s - 1) / s * (log (4.225 - s) - log (s + 1)) := by
    intro s hs; ring
  rw [intervalIntegral.integral_congr hpt2,
    intervalIntegral.integral_add ((hInt1.mul_const (log 4.225)) ) hInt2,
    intervalIntegral.integral_mul_const]
  have hpt3 : ∀ s ∈ Set.uIcc (2 : ℝ) (4.225 - 1),
      log (s - 1) / s * (log (4.225 - s) - log (s + 1)) =
        -(log (s - 1) / s * (log (s + 1) - log (4.225 - s))) := by
    intro s hs; ring
  rw [intervalIntegral.integral_congr hpt3, intervalIntegral.integral_neg]
  ring

/-! ### The explicit value of the coefficient, as an integral of the sieve function -/

private theorem coeff_eq_integral337 :
    sieveOneCoefficient337 =
      (22 * exp (-eulerMascheroniConstant) / 0.95) *
        ∫ u in (5.225 - 11 * (1 / 3.29))..(4.225), sieveUpper306 u / (5.225 - u) := by
  have hlo_ne : (5.225 : ℝ) - 11 * (1 / 3.29) ≠ 0 := by
    have h : (5.225 : ℝ) - 11 * (1 / 3.29) = 24761 / 13160 := by norm_num
    rw [h]; norm_num
  have hJ : (∫ t in (2 : ℝ)..(4.225 - 1),
        log (t - 1) / t * (log (t + 1) - log (5.225 - (t + 1)))) =
      ∫ t in (2 : ℝ)..(4.225 - 1), log (t - 1) / t * (log (t + 1) - log (4.225 - t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp only
    rw [show 5.225 - (t + 1) = 4.225 - t by ring]
  have hDel : (log 4.225 - (log (5.225 - 11 * (1 / 3.29)) -
        log (5.225 - (5.225 - 11 * (1 / 3.29))))) =
      log ((11 * 0.95 - 2) / (3.29 * 0.95 - 2)) := by
    have h2 : (5.225 : ℝ) - (5.225 - 11 * (1 / 3.29)) = 11 * (1 / 3.29) := by ring
    rw [h2,
      show log 4.225 - (log (5.225 - 11 * (1 / 3.29)) - log (11 * (1 / 3.29))) =
        log 4.225 - log (5.225 - 11 * (1 / 3.29)) + log (11 * (1 / 3.29)) by ring,
      ← log_div (by norm_num : (4.225 : ℝ) ≠ 0) hlo_ne,
      ← Real.log_mul (x := 4.225 / (5.225 - 11 * (1 / 3.29))) (y := 11 * (1 / 3.29))
        (by positivity) (by positivity)]
    congr 1
    norm_num
  have hcoef : (22 * exp (-eulerMascheroniConstant) / 0.95) *
      (2 * exp eulerMascheroniConstant / 5.225) = 8 / 0.95 ^ 2 := by
    rw [exp_neg]
    field_simp
    norm_num
  have hP : (∫ s in (2 : ℝ)..(5.5 * 0.95 - 2), log (s - 1) / s *
        log ((5.5 * 0.95 - 1) * (5.5 * 0.95 - 1 - s) / (s + 1))) =
      ∫ s in (2 : ℝ)..(4.225 - 1), log (s - 1) / s * log (4.225 * (4.225 - s) / (s + 1)) := by
    have h1 : (5.5 : ℝ) * 0.95 - 2 = 4.225 - 1 := by norm_num
    have h2 : (5.5 : ℝ) * 0.95 - 1 = 4.225 := by norm_num
    rw [h1, h2]
  rw [integral_F_split337, integral_K_by_parts337, integral_Kprime_phi337, hJ,
    show (5.225 : ℝ) - 4.225 = 1 by norm_num, log_one, sub_zero,
    ← integral_paper_split337]
  unfold sieveOneCoefficient337
  rw [hP, hDel, ← mul_assoc, hcoef]

/-! ### The `log p / log N` dictionary -/

private theorem rpow_le_iff_log_div337 {N p : ℕ} (hN : 1 < N) (hp : 0 < p) (c : ℝ) :
    (N : ℝ) ^ c ≤ (p : ℝ) ↔ c ≤ log p / log N := by
  have hNp : (0 : ℝ) < N := by
    have : (1 : ℝ) < N := by exact_mod_cast hN
    linarith
  have hpp : (0 : ℝ) < p := by exact_mod_cast hp
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  rw [← Real.log_le_log_iff (rpow_pos_of_pos hNp c) hpp, Real.log_rpow hNp,
    le_div_iff₀ hL]

private theorem log_div_lt_iff_rpow337 {N p : ℕ} (hN : 1 < N) (hp : 0 < p) (c : ℝ) :
    log p / log N < c ↔ (p : ℝ) < (N : ℝ) ^ c := by
  have hNp : (0 : ℝ) < N := by
    have : (1 : ℝ) < N := by exact_mod_cast hN
    linarith
  have hpp : (0 : ℝ) < p := by exact_mod_cast hp
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  rw [← Real.log_lt_log_iff hpp (rpow_pos_of_pos hNp c), Real.log_rpow hNp,
    div_lt_iff₀ hL]

/-! ### Two finite sets that differ at one end have sums at most `2B` apart -/

private theorem sum_sdiff_bound337 (β : ℕ → ℝ) (S T : Finset ℕ) (B : ℝ) (hB0 : 0 ≤ B)
    (h1 : (S \ T).card ≤ 1) (h2 : (T \ S).card ≤ 1)
    (hS : ∀ p ∈ S, |β p| ≤ B) (hT : ∀ p ∈ T, |β p| ≤ B) :
    |∑ p ∈ S, β p - ∑ p ∈ T, β p| ≤ 2 * B := by
  have hST : S \ (S ∩ T) = S \ T := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hTS : T \ (S ∩ T) = T \ S := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hSsplit : ∑ p ∈ S \ T, β p + ∑ p ∈ S ∩ T, β p = ∑ p ∈ S, β p := by
    have h := Finset.sum_sdiff (s₁ := S ∩ T) (s₂ := S) (f := β) (Finset.inter_subset_left)
    rw [hST] at h
    exact h
  have hTsplit : ∑ p ∈ T \ S, β p + ∑ p ∈ S ∩ T, β p = ∑ p ∈ T, β p := by
    have h := Finset.sum_sdiff (s₁ := S ∩ T) (s₂ := T) (f := β) (Finset.inter_subset_right)
    rw [hTS] at h
    exact h
  have key : ∀ Z : Finset ℕ, Z.card ≤ 1 → (∀ p ∈ Z, |β p| ≤ B) →
      |∑ p ∈ Z, β p| ≤ B := by
    intro Z hZ hb
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul Z (fun p => |β p|) B hb) ?_
    have hc : ((Z.card : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hZ
    calc Z.card • B = ((Z.card : ℕ) : ℝ) * B := by rw [nsmul_eq_mul]
      _ ≤ 1 * B := by gcongr
      _ = B := one_mul B
  have hb1 : |∑ p ∈ S \ T, β p| ≤ B :=
    key _ h1 (fun p hp => hS p (Finset.mem_sdiff.mp hp).1)
  have hb2 : |∑ p ∈ T \ S, β p| ≤ B :=
    key _ h2 (fun p hp => hT p (Finset.mem_sdiff.mp hp).1)
  have hdiff : ∑ p ∈ S, β p - ∑ p ∈ T, β p =
      ∑ p ∈ S \ T, β p - ∑ p ∈ T \ S, β p := by
    rw [← hSsplit, ← hTsplit]; ring
  rw [hdiff]
  calc |∑ p ∈ S \ T, β p - ∑ p ∈ T \ S, β p|
      ≤ |∑ p ∈ S \ T, β p| + |∑ p ∈ T \ S, β p| := by
        simpa using abs_sub_le (∑ p ∈ S \ T, β p) 0 (∑ p ∈ T \ S, β p)
    _ ≤ B + B := add_le_add hb1 hb2
    _ = 2 * B := by ring

/-! ### The two prime filters differ at one element at each end -/

private theorem prime_filter_sdiff_card337 {N : ℕ} {a b c : ℝ}
    (hNb : (N : ℝ) ^ b ≤ N) :
    ((((range (N + 1)).filter (fun p : ℕ =>
        p.Prime ∧ (N : ℝ) ^ a ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ b)).filter
        (fun p : ℕ => (N : ℝ) ^ c ≤ (p : ℝ))) \
      ((Ioc ⌊(N : ℝ) ^ c⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  have key : ∀ r : ℕ, r ∈ (((range (N + 1)).filter (fun p : ℕ =>
        p.Prime ∧ (N : ℝ) ^ a ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ b)).filter
        (fun p : ℕ => (N : ℝ) ^ c ≤ (p : ℝ))) \
      ((Ioc ⌊(N : ℝ) ^ c⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime) → (r : ℝ) = (N : ℝ) ^ c := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := Finset.mem_sdiff.mp hr
    have hrc : (N : ℝ) ^ c ≤ (r : ℝ) := (Finset.mem_filter.mp hr1).2
    have hinner := (Finset.mem_filter.mp hr1).1
    have hprime : r.Prime := (Finset.mem_filter.mp hinner).2.1
    have hrb : (r : ℝ) < (N : ℝ) ^ b := (Finset.mem_filter.mp hinner).2.2.2
    by_cases hA : ⌊(N : ℝ) ^ c⌋₊ < r
    · exfalso
      have hB : ¬ (r ≤ ⌊(N : ℝ) ^ b⌋₊) := by
        intro hB'
        exact hr2 (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hA, hB'⟩, hprime⟩)
      have h1 : ⌊(N : ℝ) ^ b⌋₊ + 1 ≤ r := by omega
      have h2 : (r : ℝ) < (⌊(N : ℝ) ^ b⌋₊ : ℝ) + 1 := by
        have := Nat.lt_floor_add_one ((N : ℝ) ^ b)
        push_cast
        linarith
      have h3 : (⌊(N : ℝ) ^ b⌋₊ : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast h1
      linarith
    · have hple : r ≤ ⌊(N : ℝ) ^ c⌋₊ := le_of_not_gt hA
      have h4 : (r : ℝ) ≤ (N : ℝ) ^ c :=
        le_trans (by exact_mod_cast hple) (Nat.floor_le (by positivity))
      linarith
  have : (p : ℝ) = (q : ℝ) := by rw [key p hp, key q hq]
  exact_mod_cast this

private theorem prime_filter_sdiff_card337' {N : ℕ} {a b c : ℝ} (hac : a ≤ c) (hcb : c < b)
    (hNb : (N : ℝ) ^ b ≤ N) :
    (((Ioc ⌊(N : ℝ) ^ c⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime) \
      (((range (N + 1)).filter (fun p : ℕ =>
        p.Prime ∧ (N : ℝ) ^ a ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ b)).filter
        (fun p : ℕ => (N : ℝ) ^ c ≤ (p : ℝ)))).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  have key : ∀ r : ℕ, r ∈ ((Ioc ⌊(N : ℝ) ^ c⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime) \
      (((range (N + 1)).filter (fun p : ℕ =>
        p.Prime ∧ (N : ℝ) ^ a ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ b)).filter
        (fun p : ℕ => (N : ℝ) ^ c ≤ (p : ℝ))) → (r : ℝ) = (N : ℝ) ^ b := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := Finset.mem_sdiff.mp hr
    obtain ⟨hrIoc, hprime⟩ := Finset.mem_filter.mp hr1
    obtain ⟨hrc, hrb⟩ := Finset.mem_Ioc.mp hrIoc
    have hrge : (N : ℝ) ^ c ≤ (r : ℝ) := by
      have h5 : (⌊(N : ℝ) ^ c⌋₊ : ℝ) + 1 ≤ (r : ℝ) := by
        exact_mod_cast (show ⌊(N : ℝ) ^ c⌋₊ + 1 ≤ r by omega)
      have h6 : (N : ℝ) ^ c < (⌊(N : ℝ) ^ c⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      linarith
    have hle : (r : ℝ) ≤ (N : ℝ) ^ b := by
      have h3 : (⌊(N : ℝ) ^ b⌋₊ : ℝ) ≤ (N : ℝ) ^ b := Nat.floor_le (by positivity)
      exact le_trans (by exact_mod_cast hrb) h3
    by_contra hne
    have hrlt : (r : ℝ) < (N : ℝ) ^ b := lt_of_le_of_ne hle hne
    have hmem : r ∈ ((range (N + 1)).filter (fun p : ℕ =>
        p.Prime ∧ (N : ℝ) ^ a ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ b)).filter
        (fun p : ℕ => (N : ℝ) ^ c ≤ (p : ℝ)) := by
      have hN1 : (1 : ℝ) ≤ N := by
        have h2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hprime.two_le
        linarith [hle, hNb]
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hprime,
        le_trans (rpow_le_rpow_of_exponent_le hN1 hac) hrge, hrlt⟩, hrge⟩
      have hrN : (r : ℝ) < (N : ℝ) := lt_of_lt_of_le hrlt hNb
      have : r < N := by exact_mod_cast hrN
      omega
    exact hr2 hmem
  have : (p : ℝ) = (q : ℝ) := by rw [key p hp, key q hq]
  exact_mod_cast this

/-- The leaf's own prime filter, cut at a threshold `N^c`, differs from the clean
block `Ioc ⌊N^c⌋ ⌊N^b⌋` by at most `2 / N^a` in reciprocal mass. -/
private theorem leaf_vs_Ioc337 (N : ℕ) (a b c : ℝ) (ha : 0 < a) (hac : a ≤ c) (hcb : c < b)
    (hb1 : b ≤ 1) (hN2 : 2 ≤ N) :
    |((((range (N + 1)).filter (fun p : ℕ =>
            p.Prime ∧ (N : ℝ) ^ a ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ b)).filter
            (fun p : ℕ => (N : ℝ) ^ c ≤ (p : ℝ))).sum (fun p : ℕ => (1 : ℝ) / (p : ℝ)))
        - (((Ioc ⌊(N : ℝ) ^ c⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime).sum
            (fun p : ℕ => (1 : ℝ) / (p : ℝ)))| ≤
      2 * ((N : ℝ) ^ a)⁻¹ := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN2
  have hNp : (0 : ℝ) < N := by linarith
  have hNb : (N : ℝ) ^ b ≤ N := by
    have h1 : (N : ℝ) ^ b ≤ (N : ℝ) ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hN1.le hb1
    simpa using h1
  refine sum_sdiff_bound337 (fun p : ℕ => (1 : ℝ) / (p : ℝ)) _ _ _ (by positivity)
    (prime_filter_sdiff_card337 hNb) (prime_filter_sdiff_card337' hac hcb hNb) ?_ ?_
  · intro p hp
    have hpc : (N : ℝ) ^ c ≤ (p : ℝ) := (Finset.mem_filter.mp hp).2
    have hpge : (N : ℝ) ^ a ≤ (p : ℝ) :=
      le_trans (rpow_le_rpow_of_exponent_le hN1.le hac) hpc
    have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le (rpow_pos_of_pos hNp a) hpge
    rw [abs_of_pos (by positivity)]
    simpa [one_div] using inv_anti₀ (rpow_pos_of_pos hNp a) hpge
  · intro p hp
    obtain ⟨hIoc, -⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpc, -⟩ := Finset.mem_Ioc.mp hIoc
    have h1 : (⌊(N : ℝ) ^ c⌋₊ : ℝ) + 1 ≤ (p : ℝ) := by
      exact_mod_cast (show ⌊(N : ℝ) ^ c⌋₊ + 1 ≤ p by omega)
    have h2 : (N : ℝ) ^ c < (⌊(N : ℝ) ^ c⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hpge : (N : ℝ) ^ a ≤ (p : ℝ) :=
      le_trans (rpow_le_rpow_of_exponent_le hN1.le hac) (le_of_lt (lt_of_lt_of_le h2 h1))
    have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le (rpow_pos_of_pos hNp a) hpge
    rw [abs_of_pos (by positivity)]
    simpa [one_div] using inv_anti₀ (rpow_pos_of_pos hNp a) hpge

/-- The clean block limit, restated for the threshold `c`. -/
private theorem leaf_partial_tendsto337 (a b c : ℝ) (ha : 0 < a) (hac : a ≤ c) (hcb : c < b) :
    Tendsto (fun N : ℕ => ((Ioc ⌊(N : ℝ) ^ c⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime).sum
        (fun p : ℕ => (1 : ℝ) / (p : ℝ))) atTop (𝓝 (log (b / c))) :=
  prime_reciprocal_block_limit337 c b (ha.trans_le hac) hcb

/-- The same limit for the leaf's own filter: the two-point correction is `O (N^-a)`. -/
private theorem leaf_partial_tendsto_leaf337 (a b c : ℝ) (ha : 0 < a) (hac : a ≤ c) (hcb : c < b)
    (hb1 : b ≤ 1) :
    Tendsto (fun N : ℕ =>
        let S : Finset ℕ := (((range (N + 1)).filter (fun p : ℕ =>
          p.Prime ∧ (N : ℝ) ^ a ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ b)).filter
          (fun p : ℕ => (N : ℝ) ^ c ≤ (p : ℝ)));
        S.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ))) atTop (𝓝 (log (b / c))) := by
  have hNp : Tendsto (fun N : ℕ => ((N : ℝ) ^ a)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    have h0 : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
      (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp h0
  have hdiff : Tendsto (fun N : ℕ =>
      (let S : Finset ℕ := (((range (N + 1)).filter (fun p : ℕ =>
          p.Prime ∧ (N : ℝ) ^ a ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ b)).filter
          (fun p : ℕ => (N : ℝ) ^ c ≤ (p : ℝ)));
        S.sum (fun p : ℕ => (1 : ℝ) / (p : ℝ)))
      - ((Ioc ⌊(N : ℝ) ^ c⌋₊ ⌊(N : ℝ) ^ b⌋₊).filter Nat.Prime).sum
          (fun p : ℕ => (1 : ℝ) / (p : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    have hb : Tendsto (fun N : ℕ => 2 * ((N : ℝ) ^ a)⁻¹) atTop (𝓝 (0 : ℝ)) := by
      simpa using hNp.const_mul (2 : ℝ)
    refine squeeze_zero_norm' (a := fun N : ℕ => 2 * ((N : ℝ) ^ a)⁻¹) ?_ hb
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact leaf_vs_Ioc337 N a b c ha hac hcb hb1 hN
  have h := (leaf_partial_tendsto337 a b c ha hac hcb).add hdiff
  simpa using h


/-! ### The grid: block index of a point, and the telescoping identity for step sums -/

private theorem step_index337 {a h t : ℝ} {k : ℕ} (hh : 0 < h) (hat : a ≤ t)
    (htb : t ≤ a + (k : ℝ) * h) :
    a + ((min k ⌊(t - a) / h⌋₊ : ℕ) : ℝ) * h ≤ t ∧
      t < a + (((min k ⌊(t - a) / h⌋₊ : ℕ) : ℝ) + 1) * h := by
  have h0 : (0 : ℝ) ≤ (t - a) / h := div_nonneg (by linarith) hh.le
  have hfloor : ((⌊(t - a) / h⌋₊ : ℕ) : ℝ) ≤ (t - a) / h := Nat.floor_le h0
  have hupper : (t - a) / h < ((⌊(t - a) / h⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmin : ((min k ⌊(t - a) / h⌋₊ : ℕ) : ℝ) ≤ ((⌊(t - a) / h⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast min_le_right k ⌊(t - a) / h⌋₊
  constructor
  · have h3 : ((min k ⌊(t - a) / h⌋₊ : ℕ) : ℝ) * h ≤ t - a := by
      have h4 : ((min k ⌊(t - a) / h⌋₊ : ℕ) : ℝ) * h ≤ ((⌊(t - a) / h⌋₊ : ℕ) : ℝ) * h :=
        mul_le_mul_of_nonneg_right hmin hh.le
      have h5 : ((⌊(t - a) / h⌋₊ : ℕ) : ℝ) * h ≤ t - a := (le_div_iff₀ hh).mp hfloor
      linarith
    linarith
  · by_cases hmk : ⌊(t - a) / h⌋₊ ≤ k
    · have hmeq : min k ⌊(t - a) / h⌋₊ = ⌊(t - a) / h⌋₊ := min_eq_right hmk
      rw [hmeq]
      have h5 : (t - a) / h * h < (((⌊(t - a) / h⌋₊ : ℕ) : ℝ) + 1) * h :=
        mul_lt_mul_of_pos_right hupper hh
      have h6 : (t - a) / h * h = t - a := div_mul_cancel₀ _ (ne_of_gt hh)
      linarith
    · have hkm : k < ⌊(t - a) / h⌋₊ := not_le.mp hmk
      have hmeq : min k ⌊(t - a) / h⌋₊ = k := min_eq_left hkm.le
      rw [hmeq]
      push_cast
      linarith

private theorem step_telescope337 (f x : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ Finset.range k, f i * (x (i + 1) - x i) =
      f 0 * (x k - x 0) +
        ∑ i ∈ Finset.range k, (f (i + 1) - f i) * (x k - x (i + 1)) := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hshift : ∑ i ∈ Finset.range n, (f (i + 1) - f i) * (x (n + 1) - x (i + 1)) =
        ∑ i ∈ Finset.range n, (f (i + 1) - f i) * (x n - x (i + 1)) +
          (∑ i ∈ Finset.range n, (f (i + 1) - f i)) * (x (n + 1) - x n) := by
      rw [Finset.sum_mul]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have htel : ∑ i ∈ Finset.range n, (f (i + 1) - f i) = f n - f 0 :=
      Finset.sum_range_sub f n
    simp only [Finset.sum_range_succ]
    rw [ih, hshift, htel]
    ring

/-- Telescoping over the indices above `m`, weighted by the indicator of `m ≤ i`. -/
private theorem step_core337 (F : ℕ → ℝ) {k m : ℕ} (hm : m ≤ k) :
    ∑ i ∈ Finset.range k, (F (i + 1) - F i) * (if m ≤ i then (1 : ℝ) else 0) =
      F k - F m := by
  have hfil : (Finset.range k).filter (fun i => m ≤ i) = Finset.range k \ Finset.range m := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff]
    omega
  have hstep : ∑ i ∈ Finset.range k, (F (i + 1) - F i) * (if m ≤ i then (1 : ℝ) else 0) =
      ∑ i ∈ (Finset.range k).filter (fun i => m ≤ i), (F (i + 1) - F i) := by
    have hcongr : ∑ i ∈ Finset.range k, (F (i + 1) - F i) * (if m ≤ i then (1 : ℝ) else 0) =
        ∑ i ∈ Finset.range k, (if m ≤ i then (F (i + 1) - F i) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring
    rw [hcongr, ← Finset.sum_filter]
  rw [hstep, hfil]
  have hsplit := Finset.sum_sdiff (s₁ := Finset.range m) (s₂ := Finset.range k)
    (f := fun i => (F (i + 1) - F i)) (Finset.range_subset_range.mpr hm)
  have hk := Finset.sum_range_sub F k
  have hmm := Finset.sum_range_sub F m
  linarith

/-- The step function `f (a + k h) - Σ_i Δ_i [t < a + (i+1) h]` is within `ω` of `f` on the grid. -/
private theorem step_pointwise337 (f : ℝ → ℝ) {a h : ℝ} {k : ℕ} (hh : 0 < h) (t ω : ℝ)
    (hat : a ≤ t) (htb : t ≤ a + (k : ℝ) * h)
    (huc : ∀ x ∈ Set.Icc a (a + (k : ℝ) * h), ∀ y ∈ Set.Icc a (a + (k : ℝ) * h),
      |x - y| < h → |f x - f y| ≤ ω) :
    |f t - (f (a + (k : ℝ) * h) - ∑ i ∈ Finset.range k,
        (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) *
          (if t < a + ((i : ℝ) + 1) * h then (1 : ℝ) else 0))| ≤ ω := by
  set m : ℕ := min k ⌊(t - a) / h⌋₊ with hmdef
  obtain ⟨hm1, hm2⟩ := step_index337 (k := k) hh hat htb
  have hmle : m ≤ k := min_le_left k _
  have hmcast : ((m : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmle
  have hid : ∀ i ∈ Finset.range k,
      (t < a + ((i : ℝ) + 1) * h) ↔ (m ≤ i) := by
    intro i _
    constructor
    · intro hlt
      have h2 : (m : ℝ) * h < ((i : ℝ) + 1) * h := by
        have h1 : a + (m : ℝ) * h < a + ((i : ℝ) + 1) * h := lt_of_le_of_lt hm1 hlt
        linarith
      have h3 : (m : ℝ) < ((i : ℝ) + 1) := by
        by_contra hcon
        push_neg at hcon
        have h4 : ((i : ℝ) + 1) * h ≤ (m : ℝ) * h := mul_le_mul_of_nonneg_right hcon hh.le
        linarith
      have hZ : (m : ℤ) < (i : ℤ) + 1 := by exact_mod_cast h3
      have hZle : (m : ℤ) ≤ (i : ℤ) := by omega
      exact_mod_cast hZle
    · intro hmi
      have h1 : a + ((m : ℝ) + 1) * h ≤ a + ((i : ℝ) + 1) * h := by
        have hcast : ((m : ℝ) + 1) ≤ ((i : ℝ) + 1) := by
          have : (m : ℝ) ≤ (i : ℝ) := by exact_mod_cast hmi
          linarith
        nlinarith [hh]
      linarith
  have hsum : ∑ i ∈ Finset.range k,
      (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) *
        (if t < a + ((i : ℝ) + 1) * h then (1 : ℝ) else 0) =
      ∑ i ∈ Finset.range k, (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) *
        (if m ≤ i then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiff := hid i hi
    by_cases h : t < a + ((i : ℝ) + 1) * h
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
  rw [hsum]
  have hcore : ∑ i ∈ Finset.range k, (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) *
      (if m ≤ i then (1 : ℝ) else 0) = f (a + (k : ℝ) * h) - f (a + (m : ℝ) * h) := by
    have hsame : ∑ i ∈ Finset.range k, (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) *
        (if m ≤ i then (1 : ℝ) else 0) =
        ∑ i ∈ Finset.range k, ((fun j : ℕ => f (a + (j : ℝ) * h)) (i + 1) -
          (fun j : ℕ => f (a + (j : ℝ) * h)) i) * (if m ≤ i then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      beta_reduce
      rw [show ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 by push_cast; ring]
    rw [hsame, step_core337 (fun j : ℕ => f (a + (j : ℝ) * h)) hmle]
  rw [hcore]
  have hmem1 : t ∈ Set.Icc a (a + (k : ℝ) * h) := ⟨hat, htb⟩
  have hmem2 : a + (m : ℝ) * h ∈ Set.Icc a (a + (k : ℝ) * h) :=
    ⟨by nlinarith [hh], by nlinarith [hh, hmcast]⟩
  have hdist : |t - (a + (m : ℝ) * h)| < h := by
    rw [abs_lt]
    constructor <;> linarith
  have hfin := huc t hmem1 (a + (m : ℝ) * h) hmem2 hdist
  convert hfin using 2
  ring

/-- A reciprocal sum splits at a real threshold into the part below and the part above. -/
private theorem sum_ite_compl337 (S : Finset ℕ) (c : ℝ) :
    ∑ p ∈ S, (if (p : ℝ) < c then (1 : ℝ) / (p : ℝ) else 0) +
        ∑ p ∈ S, (if c ≤ (p : ℝ) then (1 : ℝ) / (p : ℝ) else 0) =
      ∑ p ∈ S, (1 : ℝ) / (p : ℝ) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : (p : ℝ) < c
  · rw [if_pos h, if_neg (not_le.mpr h)]; ring
  · rw [if_neg h, if_pos (le_of_not_gt h)]; ring

/-- The weighted sum of the step approximation is an explicit combination of the
reciprocal partial sums at the grid points. -/
private theorem step_sum_identity337 (S : Finset ℕ) {N : ℕ} (hN : 1 < N) (f : ℝ → ℝ)
    {a h : ℝ} {k : ℕ} (hS : ∀ p ∈ S, 1 ≤ p) :
    ∑ p ∈ S, (f (a + (k : ℝ) * h) -
        ∑ i ∈ Finset.range k, (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) *
          (if log p / log N < a + ((i : ℝ) + 1) * h then (1 : ℝ) else 0)) / (p : ℝ) =
      f (a + (k : ℝ) * h) * (∑ p ∈ S, (1 : ℝ) / (p : ℝ)) -
        ∑ i ∈ Finset.range k, (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) *
          (∑ p ∈ S, (if (p : ℝ) < (N : ℝ) ^ (a + ((i : ℝ) + 1) * h) then
            (1 : ℝ) / (p : ℝ) else 0)) := by
  have hstep1 : ∑ p ∈ S, (f (a + (k : ℝ) * h) -
        ∑ i ∈ Finset.range k, (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) *
          (if log p / log N < a + ((i : ℝ) + 1) * h then (1 : ℝ) else 0)) / (p : ℝ) =
      ∑ p ∈ S, (f (a + (k : ℝ) * h) -
        ∑ i ∈ Finset.range k, (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) *
          (if (p : ℝ) < (N : ℝ) ^ (a + ((i : ℝ) + 1) * h) then (1 : ℝ) else 0)) / (p : ℝ) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hcond : ∑ i ∈ Finset.range k, (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) *
          (if log p / log N < a + ((i : ℝ) + 1) * h then (1 : ℝ) else 0) =
        ∑ i ∈ Finset.range k, (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) *
          (if (p : ℝ) < (N : ℝ) ^ (a + ((i : ℝ) + 1) * h) then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      have hiff := log_div_lt_iff_rpow337 hN (hS p hp) (a + ((i : ℝ) + 1) * h)
      rw [if_congr hiff rfl rfl]
    rw [hcond]
  rw [hstep1]
  have hstep2 : ∀ p ∈ S, (f (a + (k : ℝ) * h) -
        ∑ i ∈ Finset.range k, (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) *
          (if (p : ℝ) < (N : ℝ) ^ (a + ((i : ℝ) + 1) * h) then (1 : ℝ) else 0)) / (p : ℝ) =
      f (a + (k : ℝ) * h) * (1 / (p : ℝ)) -
        ∑ i ∈ Finset.range k, (if (p : ℝ) < (N : ℝ) ^ (a + ((i : ℝ) + 1) * h) then
          (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) / (p : ℝ) else 0) := by
    intro p _
    have hinner : ∑ i ∈ Finset.range k, (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) *
          (if (p : ℝ) < (N : ℝ) ^ (a + ((i : ℝ) + 1) * h) then (1 : ℝ) else 0) =
        ∑ i ∈ Finset.range k, (if (p : ℝ) < (N : ℝ) ^ (a + ((i : ℝ) + 1) * h) then
          (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring
    rw [hinner, sub_div]
    have hfin : (∑ i ∈ Finset.range k, (if (p : ℝ) < (N : ℝ) ^ (a + ((i : ℝ) + 1) * h) then
          (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) else 0)) / (p : ℝ) =
        ∑ i ∈ Finset.range k, (if (p : ℝ) < (N : ℝ) ^ (a + ((i : ℝ) + 1) * h) then
          (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) / (p : ℝ) else 0) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring
    rw [hfin]
    simp only [one_div, div_eq_mul_inv]
    ring
  rw [Finset.sum_congr rfl hstep2, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.mul_sum]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> ring

/-! ### The integral side: the grid sum against `∫ f t / t` -/

/-- One block: the integral of `f t / t` over `[x, y]` is `f x log (y / x)` up to the
oscillation of `f` over the block. -/
private theorem block_bound337 (f : ℝ → ℝ) {x y ω : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hω : 0 ≤ ω)
    (hint : IntervalIntegrable (fun t : ℝ => f t / t) MeasureTheory.volume x y)
    (hosc : ∀ t ∈ Set.Icc x y, |f t - f x| ≤ ω) :
    |(∫ t in x..y, f t / t) - f x * (log y - log x)| ≤ ω * (log y - log x) := by
  have hzero : (0 : ℝ) ∉ Set.uIcc x y := by
    intro h
    rw [Set.uIcc_of_le hxy] at h
    exact absurd h.1 (not_le.mpr hx)
  have hlog : ∫ t in x..y, (1 : ℝ) / t = log y - log x := by
    rw [integral_one_div hzero, Real.log_div (by linarith) hx.ne']
  have hg1 : IntervalIntegrable (fun t : ℝ => f x * (1 / t)) MeasureTheory.volume x y := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht
    have hm : t ∈ Set.Icc x y := by simpa [Set.uIcc_of_le hxy] using ht
    exact ne_of_gt (lt_of_lt_of_le hx hm.1)
  have hg3 : IntervalIntegrable (fun t : ℝ => (f t - f x) / t) MeasureTheory.volume x y := by
    have hh := hint.sub hg1
    convert hh using 1
    funext t
    ring
  have hcomp : (∫ t in x..y, f t / t) =
      f x * (log y - log x) + ∫ t in x..y, (f t - f x) / t := by
    have hpt : ∀ t : ℝ, f t / t = f x * (1 / t) + (f t - f x) / t := by
      intro t; ring
    calc (∫ t in x..y, f t / t)
        = ∫ t in x..y, (f x * (1 / t) + (f t - f x) / t) :=
          intervalIntegral.integral_congr (fun t _ => hpt t)
      _ = (∫ t in x..y, f x * (1 / t)) + ∫ t in x..y, (f t - f x) / t := by
          rw [intervalIntegral.integral_add hg1 hg3]
      _ = f x * (log y - log x) + ∫ t in x..y, (f t - f x) / t := by
          rw [intervalIntegral.integral_const_mul, hlog]
  have hg4 : IntervalIntegrable (fun t : ℝ => ω / t) MeasureTheory.volume x y := by
    have hfun : (fun t : ℝ => ω / t) = fun t => ω * (1 / t) := by funext t; ring
    rw [hfun]
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht
    have hm : t ∈ Set.Icc x y := by simpa [Set.uIcc_of_le hxy] using ht
    exact ne_of_gt (lt_of_lt_of_le hx hm.1)
  have hval : (∫ t in x..y, ω / t) = ω * (log y - log x) := by
    have hfun : (fun t : ℝ => ω / t) = fun t => ω * (1 / t) := by funext t; ring
    rw [hfun, intervalIntegral.integral_const_mul, hlog]
  rw [hcomp]
  have hstep : f x * (log y - log x) + (∫ t in x..y, (f t - f x) / t) -
      f x * (log y - log x) = ∫ t in x..y, (f t - f x) / t := by ring
  rw [hstep, ← hval]
  refine le_trans (intervalIntegral.abs_integral_le_integral_abs hxy) ?_
  apply intervalIntegral.integral_mono_on hxy hg3.abs hg4
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le hx ht.1
  rw [abs_div, abs_of_pos ht0, div_le_div_iff_of_pos_right ht0]
  exact hosc t ht

/-- The grid sum of `f` against the logarithmic mesh sizes is within `ω log (b/a)` of the
integral of `f t / t`. -/
private theorem grid_integral_approx337 (f : ℝ → ℝ) {a b h ω : ℝ} {k : ℕ} (hk : 0 < k)
    (hh : 0 < h) (hb : a + (k : ℝ) * h = b) (ha : 0 < a) (hω : 0 ≤ ω)
    (hint : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
      IntervalIntegrable (fun t : ℝ => f t / t) MeasureTheory.volume u v)
    (huc : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |x - y| ≤ h → |f x - f y| ≤ ω) :
    |(∑ i ∈ Finset.range k, f (a + (i : ℝ) * h) *
        (log (a + ((i : ℝ) + 1) * h) - log (a + (i : ℝ) * h))) -
      ∫ t in a..b, f t / t| ≤ ω * log (b / a) := by
  have hmem : ∀ i ≤ k, a + (i : ℝ) * h ∈ Set.Icc a b := by
    intro i hi
    have hi' : (i : ℝ) ≤ (k : ℝ) := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have h1 : a ≤ a + (i : ℝ) * h := by
      have := mul_nonneg hi0 hh.le
      linarith
    have h2 : a + (i : ℝ) * h ≤ b := by
      rw [← hb]
      nlinarith [hh, hi']
    exact ⟨h1, h2⟩
  have hmem' : ∀ i : ℕ, i + 1 ≤ k → a + ((i : ℝ) + 1) * h ∈ Set.Icc a b := by
    intro i hi
    have h1 : a + ((i + 1 : ℕ) : ℝ) * h ∈ Set.Icc a b := hmem (i + 1) hi
    have h2 : a + ((i + 1 : ℕ) : ℝ) * h = a + ((i : ℝ) + 1) * h := by
      push_cast
      ring
    rwa [h2] at h1
  have hpos : ∀ i ≤ k, (0 : ℝ) < a + (i : ℝ) * h := by
    intro i hi
    have h1 := (hmem i hi).1
    linarith
  have hpos' : ∀ i : ℕ, i + 1 ≤ k → (0 : ℝ) < a + ((i : ℝ) + 1) * h := by
    intro i hi
    have h1 := (hmem' i hi).1
    linarith
  have hle : ∀ i < k, a + (i : ℝ) * h ≤ a + ((i : ℝ) + 1) * h := by
    intro i _
    have h1 : (i : ℝ) * h ≤ (i : ℝ) * h + h := le_add_of_nonneg_right hh.le
    have h2 : (i : ℝ) * h + h = ((i : ℝ) + 1) * h := by ring
    linarith
  have hblock : ∀ i ∈ Finset.range k,
      |f (a + (i : ℝ) * h) *
          (log (a + ((i : ℝ) + 1) * h) - log (a + (i : ℝ) * h)) -
        (∫ t in (a + (i : ℝ) * h)..(a + ((i : ℝ) + 1) * h), f t / t)| ≤
      ω * (log (a + ((i : ℝ) + 1) * h) - log (a + (i : ℝ) * h)) := by
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have hosc : ∀ t ∈ Set.Icc (a + (i : ℝ) * h) (a + ((i : ℝ) + 1) * h),
        |f t - f (a + (i : ℝ) * h)| ≤ ω := by
      intro t ht
      have htm : t ∈ Set.Icc a b := by
        refine ⟨le_trans (hmem i (le_of_lt hik)).1 ht.1, ?_⟩
        rw [← hb]
        have h2 : (i : ℝ) + 1 ≤ (k : ℝ) := by
          have : i + 1 ≤ k := Nat.succ_le_of_lt hik
          exact_mod_cast this
        nlinarith [hh, ht.2]
      have hd : |t - (a + (i : ℝ) * h)| ≤ h := by
        rw [abs_le]
        constructor <;> linarith [ht.1, ht.2]
      exact huc t htm (a + (i : ℝ) * h) (hmem i (le_of_lt hik)) hd
    rw [abs_sub_comm]
    exact block_bound337 f (hpos i (le_of_lt hik)) (hle i hik) hω
      (hint _ (hmem i (le_of_lt hik)) _ (hmem' i (Nat.succ_le_of_lt hik))) hosc
  have hsplit : ∀ m ≤ k, (∑ i ∈ Finset.range m,
      (∫ t in (a + (i : ℝ) * h)..(a + ((i : ℝ) + 1) * h), f t / t)) =
      ∫ t in a..(a + (m : ℝ) * h), f t / t := by
    intro m hm
    induction m with
    | zero =>
      have h0 : a + ((0 : ℕ) : ℝ) * h = a := by norm_num
      simp [h0]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih (Nat.le_of_succ_le hm)]
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have hfirst : IntervalIntegrable (fun t : ℝ => f t / t) MeasureTheory.volume
          a (a + (n : ℝ) * h) := by
        have h0 : a + ((0 : ℕ) : ℝ) * h = a := by norm_num
        simpa [h0] using hint _ (hmem 0 (Nat.zero_le k)) _ (hmem n (by omega))
      have hsecond : IntervalIntegrable (fun t : ℝ => f t / t) MeasureTheory.volume
          (a + (n : ℝ) * h) (a + ((n : ℝ) + 1) * h) :=
        hint _ (hmem n (by omega)) _ (hmem' n (by omega))
      rw [← intervalIntegral.integral_add_adjacent_intervals hfirst hsecond]
  have hkk : (∑ i ∈ Finset.range k,
      (∫ t in (a + (i : ℝ) * h)..(a + ((i : ℝ) + 1) * h), f t / t)) =
      ∫ t in a..b, f t / t := by
    rw [hsplit k le_rfl, hb]
  have hfin : (∑ i ∈ Finset.range k, f (a + (i : ℝ) * h) *
        (log (a + ((i : ℝ) + 1) * h) - log (a + (i : ℝ) * h))) -
      ∫ t in a..b, f t / t =
      ∑ i ∈ Finset.range k, (f (a + (i : ℝ) * h) *
        (log (a + ((i : ℝ) + 1) * h) - log (a + (i : ℝ) * h)) -
        ∫ t in (a + (i : ℝ) * h)..(a + ((i : ℝ) + 1) * h), f t / t) := by
    rw [← hkk, Finset.sum_sub_distrib]
  rw [hfin]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hblock) ?_
  have hgen : ∀ m : ℕ, (∑ i ∈ Finset.range m,
      (log (a + ((i : ℝ) + 1) * h) - log (a + (i : ℝ) * h))) =
      log (a + (m : ℝ) * h) - log a := by
    intro m
    induction m with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : a + ((n : ℝ) + 1) * h = a + ((n + 1 : ℕ) : ℝ) * h := by push_cast; ring
      rw [h1]
      ring
  have htel : (∑ i ∈ Finset.range k,
      (log (a + ((i : ℝ) + 1) * h) - log (a + (i : ℝ) * h))) = log (b / a) := by
    have hbpos : (0 : ℝ) < b := by
      have h1 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have h2 : (0 : ℝ) < (k : ℝ) * h := mul_pos h1 hh
      linarith [hb, ha, h2]
    rw [hgen k, hb, Real.log_div (ne_of_gt hbpos) ha.ne']
  rw [← Finset.mul_sum, htel]

/-- The limiting combination of the two grids agrees with the grid sum: the summation-by-parts
identity `step_telescope337` applied to `x i = log (a + i h)`. -/
private theorem limit_comb_eq_grid337 (f : ℝ → ℝ) {a b h : ℝ} {k : ℕ} (hh : 0 < h)
    (hb : a + (k : ℝ) * h = b) (ha : 0 < a) :
    f b * log (b / a) -
        ∑ i ∈ Finset.range k, (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) *
          (log (b / a) - log (b / (a + ((i : ℝ) + 1) * h))) =
      ∑ i ∈ Finset.range k, f (a + (i : ℝ) * h) *
        (log (a + ((i : ℝ) + 1) * h) - log (a + (i : ℝ) * h)) := by
  -- positivity of the grid points
  have hbpos : (0 : ℝ) < b := by
    have h1 : (0 : ℝ) ≤ (k : ℝ) * h := by
      have := Nat.cast_nonneg (α := ℝ) k
      positivity
    linarith
  have hcpos : ∀ i : ℕ, (0 : ℝ) < a + ((i : ℝ) + 1) * h := by
    intro i
    have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    nlinarith [hh, ha]
  have hL : log (b / a) = log b - log a :=
    Real.log_div (ne_of_gt hbpos) ha.ne'
  have hc : ∀ i : ℕ, log (b / (a + ((i : ℝ) + 1) * h)) =
      log b - log (a + ((i : ℝ) + 1) * h) := by
    intro i
    exact Real.log_div (ne_of_gt hbpos) (hcpos i).ne'
  -- the summation-by-parts identity
  have hcast1 : ∀ i : ℕ, ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := fun i => by push_cast; ring
  have htel := step_telescope337 (fun i : ℕ => f (a + (i : ℝ) * h))
    (fun i : ℕ => log (a + (i : ℝ) * h)) k
  simp only [hcast1] at htel
  -- the total increment
  have hsumgen : ∀ m : ℕ, (∑ i ∈ Finset.range m,
      (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h))) = f (a + (m : ℝ) * h) - f a := by
    intro m
    induction m with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : a + ((n : ℝ) + 1) * h = a + ((n + 1 : ℕ) : ℝ) * h := by push_cast; ring
      rw [h1]
      ring
  have hsumΔ : (∑ i ∈ Finset.range k, (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h))) =
      f b - f a := by
    rw [hsumgen k, hb]
  -- rewrite the summands
  have hterm : ∀ i ∈ Finset.range k,
      (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) *
        (log (b / a) - log (b / (a + ((i : ℝ) + 1) * h))) =
      (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) *
        (log (a + ((i : ℝ) + 1) * h) - log a) := by
    intro i _
    rw [hL, hc i]
    ring
  rw [Finset.sum_congr rfl hterm, htel]
  -- both sides are now explicit; kill the difference with the total increment
  have hsplit : (∑ i ∈ Finset.range k,
        (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) *
          (log (a + ((i : ℝ) + 1) * h) - log a)) +
      (∑ i ∈ Finset.range k, (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) *
        (log b - log (a + ((i : ℝ) + 1) * h))) =
      (f b - f a) * (log b - log a) := by
    rw [← Finset.sum_add_distrib]
    have hpt : ∀ i ∈ Finset.range k,
        (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) *
            (log (a + ((i : ℝ) + 1) * h) - log a) +
          (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) *
            (log b - log (a + ((i : ℝ) + 1) * h)) =
        (f (a + ((i : ℝ) + 1) * h) - f (a + (i : ℝ) * h)) * (log b - log a) := by
      intro i _
      ring
    rw [Finset.sum_congr rfl hpt, ← Finset.sum_mul, hsumΔ]
  simp only [Nat.cast_zero, zero_mul, add_zero, hb] at hsplit ⊢
  rw [hL]
  linarith [hsplit]

/-! ### Continuity of the composed upper function on the prime exponent range -/

private theorem f_contOn337 {a b : ℝ} (ha : 0 < a) (hb5 : b < 5.225 / 11) :
    ContinuousOn (fun u : ℝ => sieveUpper306 (5.225 - 11 * u)) (Set.Icc a b) := by
  refine sieveFns306.2.1.comp (by fun_prop) ?_
  intro u hu
  show (0 : ℝ) < 5.225 - 11 * u
  have hub : u ≤ b := hu.2
  nlinarith

/-! ### The upper block sums at the grid thresholds -/

private theorem upper_sum_tendsto337 (k : ℕ) (h : ℝ) (hk : 0 < k) (hh : 0 < h)
    (hhb : (1 / 11 : ℝ) + (k : ℝ) * h = 1 / 3.29) {i : ℕ} (hi : i ∈ Finset.range k) :
    Tendsto (fun N : ℕ => ∑ p ∈ (((range (N + 1)).filter (fun p : ℕ =>
        p.Prime ∧ (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ (1 / 3.29 : ℝ))).filter
        (fun p : ℕ => (N : ℝ) ^ ((1 / 11 : ℝ) + ((i : ℝ) + 1) * h) ≤ (p : ℝ))),
        (1 : ℝ) / (p : ℝ)) atTop
      (𝓝 (Real.log ((1 / 3.29) / ((1 / 11 : ℝ) + ((i : ℝ) + 1) * h)))) := by
  have ha0 : (0 : ℝ) < 1 / 11 := by norm_num
  have hab : (1 / 11 : ℝ) < 1 / 3.29 := by norm_num
  have hb1 : (1 / 3.29 : ℝ) ≤ 1 := by norm_num
  have hik : i < k := Finset.mem_range.mp hi
  have hi1 : ((i : ℝ) + 1) ≤ (k : ℝ) := by
    have : i + 1 ≤ k := Nat.succ_le_of_lt hik
    exact_mod_cast this
  have hcle : (1 / 11 : ℝ) ≤ (1 / 11 : ℝ) + ((i : ℝ) + 1) * h := by
    have : (0 : ℝ) ≤ ((i : ℝ) + 1) * h := by positivity
    linarith
  have hcbr : (1 / 11 : ℝ) + ((i : ℝ) + 1) * h ≤ 1 / 3.29 := by
    rw [← hhb]
    nlinarith
  rcases lt_or_eq_of_le hcbr with hlt | heq
  · exact leaf_partial_tendsto_leaf337 (1 / 11) (1 / 3.29) ((1 / 11 : ℝ) + ((i : ℝ) + 1) * h)
      ha0 hcle hlt hb1
  · -- the threshold is the upper endpoint: the set is empty
    have hlog0 : Real.log ((1 / 3.29) / ((1 / 11 : ℝ) + ((i : ℝ) + 1) * h)) = 0 := by
      have hpos : (0 : ℝ) < (1 / 11 : ℝ) + ((i : ℝ) + 1) * h := by
        have h0 : (0 : ℝ) ≤ ((i : ℝ) + 1) * h := by positivity
        linarith
      rw [← heq]
      rw [div_self (ne_of_gt hpos), Real.log_one]
    rw [hlog0]
    refine Tendsto.congr' (Filter.Eventually.of_forall (fun N => ?_)) tendsto_const_nhds
    simp only
    have hempty : ((range (N + 1)).filter (fun p : ℕ =>
        p.Prime ∧ (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ (1 / 3.29 : ℝ))).filter
        (fun p : ℕ => (N : ℝ) ^ ((1 / 11 : ℝ) + ((i : ℝ) + 1) * h) ≤ (p : ℝ)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
      obtain ⟨-, -, -, hplt⟩ := Finset.mem_filter.mp hp1
      rw [heq] at hp2
      exact absurd hp2 (not_le.mpr hplt)
    rw [hempty]
    simp

/-! ### The grid limit of the step approximation -/

private theorem step_limit337 (k : ℕ) (h : ℝ) (hk : 0 < k) (hh : 0 < h)
    (hhb : (1 / 11 : ℝ) + (k : ℝ) * h = 1 / 3.29) :
    Tendsto (fun N : ℕ => ∑ p ∈ ((range (N + 1)).filter (fun p : ℕ =>
        p.Prime ∧ (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ (1 / 3.29 : ℝ))),
        (sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (k : ℝ) * h)) -
          ∑ i ∈ Finset.range k, (sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + ((i : ℝ) + 1) * h)) -
            sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (i : ℝ) * h))) *
            (if Real.log p / Real.log N < (1 / 11 : ℝ) + ((i : ℝ) + 1) * h then (1 : ℝ) else 0)) /
          (p : ℝ)) atTop
      (𝓝 (sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (k : ℝ) * h)) *
          Real.log ((1 / 3.29) / (1 / 11)) -
        ∑ i ∈ Finset.range k, (sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + ((i : ℝ) + 1) * h)) -
          sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (i : ℝ) * h))) *
          (Real.log ((1 / 3.29) / (1 / 11)) -
            Real.log ((1 / 3.29) / ((1 / 11 : ℝ) + ((i : ℝ) + 1) * h))))) := by
  classical
  -- the reciprocal mass of the base set
  have hSlim : Tendsto (fun N : ℕ => ∑ p ∈ ((range (N + 1)).filter (fun p : ℕ =>
      p.Prime ∧ (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ (1 / 3.29 : ℝ))),
      (1 : ℝ) / (p : ℝ)) atTop (𝓝 (Real.log ((1 / 3.29) / (1 / 11)))) := by
    have hbase := leaf_partial_tendsto_leaf337 (1 / 11) (1 / 3.29) (1 / 11)
      (by norm_num) le_rfl (by norm_num) (by norm_num)
    refine hbase.congr' (Filter.Eventually.of_forall (fun N => ?_))
    simp only
    congr 1
    exact Finset.filter_true_of_mem (fun p hp => (Finset.mem_filter.mp hp).2.2.1)
  -- the complementary prefixes
  have hQlim : ∀ i ∈ Finset.range k, Tendsto (fun N : ℕ => ∑ p ∈ ((range (N + 1)).filter (fun p : ℕ =>
      p.Prime ∧ (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ (1 / 3.29 : ℝ))),
      (if (p : ℝ) < (N : ℝ) ^ ((1 / 11 : ℝ) + ((i : ℝ) + 1) * h) then (1 : ℝ) / (p : ℝ) else 0))
      atTop (𝓝 (Real.log ((1 / 3.29) / (1 / 11)) -
        Real.log ((1 / 3.29) / ((1 / 11 : ℝ) + ((i : ℝ) + 1) * h)))) := by
    intro i hi
    have hupper := upper_sum_tendsto337 k h hk hh hhb hi
    have hbase := leaf_partial_tendsto_leaf337 (1 / 11) (1 / 3.29) (1 / 11)
      (by norm_num) le_rfl (by norm_num) (by norm_num)
    have hSlim' : Tendsto (fun N : ℕ => ∑ p ∈ ((range (N + 1)).filter (fun p : ℕ =>
        p.Prime ∧ (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ (1 / 3.29 : ℝ))),
        (1 : ℝ) / (p : ℝ)) atTop (𝓝 (Real.log ((1 / 3.29) / (1 / 11)))) := by
      refine hbase.congr' (Filter.Eventually.of_forall (fun N => ?_))
      simp only
      congr 1
      exact Finset.filter_true_of_mem (fun p hp => (Finset.mem_filter.mp hp).2.2.1)
    have hdiff := hSlim'.sub hupper
    refine hdiff.congr' (Filter.Eventually.of_forall (fun N => ?_))
    simp only
    rw [← Finset.sum_filter]
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (((range (N + 1)).filter (fun p : ℕ => p.Prime ∧ (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ) ∧
        (p : ℝ) < (N : ℝ) ^ (1 / 3.29 : ℝ))))
      (fun p : ℕ => (p : ℝ) < (N : ℝ) ^ ((1 / 11 : ℝ) + ((i : ℝ) + 1) * h))
      (fun p : ℕ => (1 : ℝ) / (p : ℝ))
    have hneg : ((range (N + 1)).filter (fun p : ℕ => p.Prime ∧ (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ) ∧
        (p : ℝ) < (N : ℝ) ^ (1 / 3.29 : ℝ))).filter
        (fun p : ℕ => ¬ (p : ℝ) < (N : ℝ) ^ ((1 / 11 : ℝ) + ((i : ℝ) + 1) * h)) =
        ((range (N + 1)).filter (fun p : ℕ => p.Prime ∧ (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ) ∧
        (p : ℝ) < (N : ℝ) ^ (1 / 3.29 : ℝ))).filter
        (fun p : ℕ => (N : ℝ) ^ ((1 / 11 : ℝ) + ((i : ℝ) + 1) * h) ≤ (p : ℝ)) := by
      apply Finset.filter_congr
      intro p _
      exact not_lt
    rw [hneg] at hsplit
    linarith [hsplit]

  -- the identity for each N
  have hpoint : ∀ᶠ N : ℕ in atTop, (∑ p ∈ ((range (N + 1)).filter (fun p : ℕ =>
        p.Prime ∧ (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ (1 / 3.29 : ℝ))),
        (sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (k : ℝ) * h)) -
          ∑ i ∈ Finset.range k, (sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + ((i : ℝ) + 1) * h)) -
            sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (i : ℝ) * h))) *
            (if Real.log p / Real.log N < (1 / 11 : ℝ) + ((i : ℝ) + 1) * h then (1 : ℝ) else 0)) /
          (p : ℝ)) =
      sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (k : ℝ) * h)) *
          (∑ p ∈ ((range (N + 1)).filter (fun p : ℕ =>
            p.Prime ∧ (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ (1 / 3.29 : ℝ))),
            (1 : ℝ) / (p : ℝ)) -
        ∑ i ∈ Finset.range k, (sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + ((i : ℝ) + 1) * h)) -
          sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (i : ℝ) * h))) *
          (∑ p ∈ ((range (N + 1)).filter (fun p : ℕ =>
            p.Prime ∧ (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ (1 / 3.29 : ℝ))),
            (if (p : ℝ) < (N : ℝ) ^ ((1 / 11 : ℝ) + ((i : ℝ) + 1) * h) then (1 : ℝ) / (p : ℝ) else 0)) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact step_sum_identity337 ((range (N + 1)).filter (fun p : ℕ =>
        p.Prime ∧ (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ (1 / 3.29 : ℝ)))
      (by omega : 1 < N) (fun u : ℝ => sieveUpper306 (5.225 - 11 * u))
      (a := (1 / 11 : ℝ)) (h := h) (k := k)
      (fun p hp => by
        have hpp : p.Prime := (Finset.mem_filter.mp hp).2.1
        have h2 := hpp.two_le
        omega)
  -- the limit of the explicit combination
  have hcomb : Tendsto (fun N : ℕ =>
      sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (k : ℝ) * h)) *
          (∑ p ∈ ((range (N + 1)).filter (fun p : ℕ =>
            p.Prime ∧ (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ (1 / 3.29 : ℝ))),
            (1 : ℝ) / (p : ℝ)) -
        ∑ i ∈ Finset.range k, (sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + ((i : ℝ) + 1) * h)) -
          sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (i : ℝ) * h))) *
          (∑ p ∈ ((range (N + 1)).filter (fun p : ℕ =>
            p.Prime ∧ (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ (1 / 3.29 : ℝ))),
            (if (p : ℝ) < (N : ℝ) ^ ((1 / 11 : ℝ) + ((i : ℝ) + 1) * h) then (1 : ℝ) / (p : ℝ) else 0)))
      atTop (𝓝 (sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (k : ℝ) * h)) *
          Real.log ((1 / 3.29) / (1 / 11)) -
        ∑ i ∈ Finset.range k, (sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + ((i : ℝ) + 1) * h)) -
          sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (i : ℝ) * h))) *
          (Real.log ((1 / 3.29) / (1 / 11)) -
            Real.log ((1 / 3.29) / ((1 / 11 : ℝ) + ((i : ℝ) + 1) * h))))) := by
    have h1 := hSlim.const_mul (sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (k : ℝ) * h)))
    have h2 := tendsto_finset_sum (Finset.range k) (fun i hi => (hQlim i hi).const_mul
      (sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + ((i : ℝ) + 1) * h)) -
        sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (i : ℝ) * h))))
    exact h1.sub h2
  exact hcomb.congr' (hpoint.mono (fun N hN => hN.symm))



private theorem abs_sub_le_add337 (a b c : ℝ) : |a - c| ≤ |a - b| + |b - c| := by
  have h : a - c = (a - b) + (b - c) := by ring
  calc |a - c| = |(a - b) + (b - c)| := by rw [h]
    _ ≤ |a - b| + |b - c| := abs_add_le _ _

/-! ### The change of variables `s = 5.225 - 11 u` -/

private theorem subst337a :
    ∫ u in (1 / 11 : ℝ)..(1 / 3.29), sieveUpper306 (5.225 - 11 * u) / u =
      ∫ s in (5.225 - 11 * (1 / 3.29))..(4.225), sieveUpper306 s / (5.225 - s) := by
  have h := intervalIntegral.integral_comp_sub_mul (f := fun s : ℝ => sieveUpper306 s / (5.225 - s))
    (c := (11 : ℝ)) (by norm_num) (d := (5.225 : ℝ)) (a := (1 / 11 : ℝ)) (b := (1 / 3.29 : ℝ))
  have hden : ∀ x : ℝ, (5.225 : ℝ) - (5.225 - 11 * x) = 11 * x := fun x => by ring
  simp only [smul_eq_mul, hden, show (5.225 : ℝ) - 11 * (1 / 11) = 4.225 by norm_num] at h
  have hstep : ∫ x in (1 / 11 : ℝ)..(1 / 3.29), sieveUpper306 (5.225 - 11 * x) / (11 * x) =
      (1 / 11) * ∫ x in (1 / 11 : ℝ)..(1 / 3.29), sieveUpper306 (5.225 - 11 * x) / x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    have hxpos : (0 : ℝ) < x := by
      rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · linarith
      · linarith
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    field_simp
  rw [hstep] at h
  rw [show (11 : ℝ)⁻¹ = 1 / 11 by norm_num] at h
  exact mul_left_cancel₀ (by norm_num : (1 / 11 : ℝ) ≠ 0) h

/-! ### The weighted prime sum over the middle block -/

private theorem prime_sum_limit337 :
    Tendsto (fun N : ℕ => ∑ p ∈ ((range (N + 1)).filter (fun p : ℕ =>
        p.Prime ∧ (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ (1 / 3.29 : ℝ))),
        sieveUpper306 (5.225 - 11 * (Real.log p / Real.log N)) / (p : ℝ)) atTop
      (𝓝 (∫ u in (1 / 11 : ℝ)..(1 / 3.29), sieveUpper306 (5.225 - 11 * u) / u)) := by
  classical
  have ha0 : (0 : ℝ) < 1 / 11 := by norm_num
  have hb5 : (1 / 3.29 : ℝ) < 5.225 / 11 := by norm_num
  have hL0 : 0 < Real.log ((1 / 3.29) / (1 / 11)) := by
    apply Real.log_pos; norm_num
  have hfont : ContinuousOn (fun u : ℝ => sieveUpper306 (5.225 - 11 * u))
      (Set.Ioo (0 : ℝ) (5.225 / 11)) := by
    refine sieveFns306.2.1.comp (by fun_prop) ?_
    intro u hu
    show (0 : ℝ) < 5.225 - 11 * u
    nlinarith [hu.2]
  have hcont' : ContinuousOn (fun t : ℝ => sieveUpper306 (5.225 - 11 * t) / t)
      (Set.Ioo (0 : ℝ) (5.225 / 11)) :=
    hfont.div continuousOn_id (fun t ht => ne_of_gt ht.1)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : 0 < ε / 4 := by linarith
  set ω : ℝ := ε / (4 * (Real.log ((1 / 3.29) / (1 / 11)) + 1)) with hωdef
  have hω1 : 0 < Real.log ((1 / 3.29) / (1 / 11)) + 1 := by linarith
  have hω0 : 0 < ω := by
    rw [hωdef]
    exact div_pos hε (by positivity)
  have hωL : ω * (Real.log ((1 / 3.29) / (1 / 11)) + 1) = ε / 4 := by
    rw [hωdef]; field_simp
  have hucall : UniformContinuousOn (fun u : ℝ => sieveUpper306 (5.225 - 11 * u))
      (Set.Icc (1 / 11) (1 / 3.29)) := by
    apply isCompact_Icc.uniformContinuousOn_of_continuous
    refine hfont.mono ?_
    intro u hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff_le.mp hucall ω hω0
  obtain ⟨k, hk0, hkh⟩ : ∃ k : ℕ, 0 < k ∧ ((1 / 3.29 : ℝ) - 1 / 11) / δ < (k : ℝ) := by
    obtain ⟨n, hn⟩ := exists_nat_gt (((1 / 3.29 : ℝ) - 1 / 11) / δ)
    exact ⟨n + 1, Nat.succ_pos n, by push_cast; linarith⟩
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  set hte : ℝ := ((1 / 3.29 : ℝ) - 1 / 11) / (k : ℝ) with hhdef
  have hh0 : 0 < hte := by
    rw [hhdef]; exact div_pos (by norm_num) hkR
  have hhδ : hte ≤ δ := by
    rw [hhdef, div_le_iff₀ hkR]
    have h2 := (div_lt_iff₀ hδ0).mp hkh
    linarith
  have hhb : (1 / 11 : ℝ) + (k : ℝ) * hte = 1 / 3.29 := by
    rw [hhdef]; field_simp; ring
  -- the oscillation bound on the grid
  have huc' : ∀ x ∈ Set.Icc (1 / 11 : ℝ) ((1 / 11 : ℝ) + (k : ℝ) * hte),
      ∀ y ∈ Set.Icc (1 / 11 : ℝ) ((1 / 11 : ℝ) + (k : ℝ) * hte),
      |x - y| ≤ hte → |sieveUpper306 (5.225 - 11 * x) - sieveUpper306 (5.225 - 11 * y)| ≤ ω := by
    intro x hx y hy hxy
    rw [hhb] at hx hy
    have h := hδ x hx y hy (le_trans hxy hhδ)
    simpa [Real.dist_eq] using h
  have huc_lt : ∀ x ∈ Set.Icc (1 / 11 : ℝ) ((1 / 11 : ℝ) + (k : ℝ) * hte),
      ∀ y ∈ Set.Icc (1 / 11 : ℝ) ((1 / 11 : ℝ) + (k : ℝ) * hte),
      |x - y| < hte → |sieveUpper306 (5.225 - 11 * x) - sieveUpper306 (5.225 - 11 * y)| ≤ ω :=
    fun x hx y hy h => huc' x hx y hy h.le
  -- integrability of the coefficient integrand
  have hint : ∀ u ∈ Set.Icc (1 / 11 : ℝ) ((1 / 11 : ℝ) + (k : ℝ) * hte),
      ∀ v ∈ Set.Icc (1 / 11 : ℝ) ((1 / 11 : ℝ) + (k : ℝ) * hte),
      IntervalIntegrable (fun t : ℝ => sieveUpper306 (5.225 - 11 * t) / t)
        MeasureTheory.volume u v := by
    intro u hu v hv
    rw [hhb] at hu hv
    have hsmall : (0 : ℝ) < min u v := lt_min (by linarith [hu.1]) (by linarith [hv.1])
    have hbig : max u v < 5.225 / 11 :=
      lt_of_le_of_lt (max_le (by linarith [hu.2]) (by linarith [hv.2])) hb5
    have hmono : ContinuousOn (fun t : ℝ => sieveUpper306 (5.225 - 11 * t) / t)
        (Set.uIcc u v) := by
      apply ContinuousOn.mono hcont'
      intro t ht
      exact ⟨lt_of_lt_of_le hsmall ht.1, lt_of_le_of_lt ht.2 hbig⟩
    exact ContinuousOn.intervalIntegrable hmono
  -- the grid sum against the integral
  have hfb : sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (k : ℝ) * hte)) =
      sieveUpper306 (5.225 - 11 * (1 / 3.29 : ℝ)) := by rw [hhb]
  have hGJ0 : |(sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (k : ℝ) * hte)) *
          Real.log (((1 / 11 : ℝ) + (k : ℝ) * hte) / (1 / 11)) -
        ∑ i ∈ Finset.range k, (sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + ((i : ℝ) + 1) * hte)) -
          sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (i : ℝ) * hte))) *
          (Real.log (((1 / 11 : ℝ) + (k : ℝ) * hte) / (1 / 11)) -
            Real.log (((1 / 11 : ℝ) + (k : ℝ) * hte) / ((1 / 11 : ℝ) + ((i : ℝ) + 1) * hte)))) -
      ∫ u in (1 / 11 : ℝ)..((1 / 11 : ℝ) + (k : ℝ) * hte), sieveUpper306 (5.225 - 11 * u) / u| ≤
      ω * Real.log (((1 / 11 : ℝ) + (k : ℝ) * hte) / (1 / 11)) := by
    have h := grid_integral_approx337 (fun u : ℝ => sieveUpper306 (5.225 - 11 * u))
      (a := (1 / 11 : ℝ)) (b := ((1 / 11 : ℝ) + (k : ℝ) * hte)) (h := hte) (k := k) (ω := ω)
      hk0 hh0 rfl ha0 hω0.le hint huc'
    rw [limit_comb_eq_grid337 (fun u : ℝ => sieveUpper306 (5.225 - 11 * u))
      (a := (1 / 11 : ℝ)) (b := ((1 / 11 : ℝ) + (k : ℝ) * hte)) (h := hte) (k := k) hh0 rfl ha0]
    exact h
  -- the two sums and the limit values
  set A : ℕ → ℝ := fun N => ∑ p ∈ ((range (N + 1)).filter (fun p : ℕ =>
      p.Prime ∧ (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ (1 / 3.29 : ℝ))),
      sieveUpper306 (5.225 - 11 * (Real.log p / Real.log N)) / (p : ℝ) with hA
  set B : ℕ → ℝ := fun N => ∑ p ∈ ((range (N + 1)).filter (fun p : ℕ =>
      p.Prime ∧ (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ (1 / 3.29 : ℝ))),
      (sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (k : ℝ) * hte)) -
          ∑ i ∈ Finset.range k, (sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + ((i : ℝ) + 1) * hte)) -
            sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (i : ℝ) * hte))) *
            (if Real.log p / Real.log N < (1 / 11 : ℝ) + ((i : ℝ) + 1) * hte then (1 : ℝ) else 0)) /
          (p : ℝ) with hB
  set S : ℕ → ℝ := fun N => ∑ p ∈ ((range (N + 1)).filter (fun p : ℕ =>
      p.Prime ∧ (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ (1 / 3.29 : ℝ))),
      (1 : ℝ) / (p : ℝ) with hS
  set L : ℝ := sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (k : ℝ) * hte)) *
          Real.log ((1 / 3.29) / (1 / 11)) -
        ∑ i ∈ Finset.range k, (sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + ((i : ℝ) + 1) * hte)) -
          sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (i : ℝ) * hte))) *
          (Real.log ((1 / 3.29) / (1 / 11)) -
            Real.log ((1 / 3.29) / ((1 / 11 : ℝ) + ((i : ℝ) + 1) * hte))) with hL
  set J : ℝ := ∫ u in (1 / 11 : ℝ)..(1 / 3.29), sieveUpper306 (5.225 - 11 * u) / u with hJ
  have hGJ : |L - J| ≤ ω * Real.log ((1 / 3.29) / (1 / 11)) := by
    rw [hL, hJ]
    have h1 := hGJ0
    rw [hhb] at h1
    rw [← hfb] at h1
    exact h1
  have hstepB : Tendsto B atTop (𝓝 L) := by
    rw [hB, hL]
    exact step_limit337 k hte hk0 hh0 hhb
  have hSlimS : Tendsto S atTop (𝓝 (Real.log ((1 / 3.29) / (1 / 11)))) := by
    rw [hS]
    refine Tendsto.congr' (Filter.Eventually.of_forall (fun N => ?_))
      (leaf_partial_tendsto_leaf337 (1 / 11) (1 / 3.29) (1 / 11)
        (by norm_num) le_rfl (by norm_num) (by norm_num))
    simp only
    congr 1
    exact Finset.filter_true_of_mem (fun p hp => (Finset.mem_filter.mp hp).2.2.1)
  -- the difference of the two sums, termwise
  have hdiff : ∀ᶠ N : ℕ in atTop, |A N - B N| ≤ ω * S N := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hN1 : 1 < N := by omega
    have hterm : ∀ p ∈ ((range (N + 1)).filter (fun p : ℕ =>
        p.Prime ∧ (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ (1 / 3.29 : ℝ))),
        |sieveUpper306 (5.225 - 11 * (Real.log p / Real.log N)) -
          (sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (k : ℝ) * hte)) -
            ∑ i ∈ Finset.range k, (sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + ((i : ℝ) + 1) * hte)) -
              sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (i : ℝ) * hte))) *
              (if Real.log p / Real.log N < (1 / 11 : ℝ) + ((i : ℝ) + 1) * hte then (1 : ℝ) else 0))| ≤ ω := by
      intro p hp
      obtain ⟨-, hprime, hpa, hpb⟩ := Finset.mem_filter.mp hp
      have hpp : 0 < p := hprime.pos
      have ht1 : (1 / 11 : ℝ) ≤ Real.log p / Real.log N :=
        (rpow_le_iff_log_div337 hN1 hpp (1 / 11)).mp hpa
      have ht2 : Real.log p / Real.log N ≤ (1 / 11 : ℝ) + (k : ℝ) * hte := by
        rw [hhb]
        exact le_of_lt ((log_div_lt_iff_rpow337 hN1 hpp (1 / 3.29)).mpr hpb)
      exact step_pointwise337 (fun u : ℝ => sieveUpper306 (5.225 - 11 * u)) hh0
        (Real.log p / Real.log N) ω ht1 ht2 huc_lt
    have hpos : ∀ p ∈ ((range (N + 1)).filter (fun p : ℕ =>
        p.Prime ∧ (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ (1 / 3.29 : ℝ))),
        (0 : ℝ) < (p : ℝ) := by
      intro p hp
      have := (Finset.mem_filter.mp hp).2.1.pos
      exact_mod_cast this
    have hsplit : A N - B N = ∑ p ∈ ((range (N + 1)).filter (fun p : ℕ =>
        p.Prime ∧ (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ (1 / 3.29 : ℝ))),
        ((sieveUpper306 (5.225 - 11 * (Real.log p / Real.log N)) -
          (sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (k : ℝ) * hte)) -
            ∑ i ∈ Finset.range k, (sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + ((i : ℝ) + 1) * hte)) -
              sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (i : ℝ) * hte))) *
              (if Real.log p / Real.log N < (1 / 11 : ℝ) + ((i : ℝ) + 1) * hte then (1 : ℝ) else 0))) /
          (p : ℝ)) := by
      rw [hA, hB, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p _
      ring
    rw [hsplit]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have h2 : ∀ p ∈ ((range (N + 1)).filter (fun p : ℕ =>
        p.Prime ∧ (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ (1 / 3.29 : ℝ))),
        |((sieveUpper306 (5.225 - 11 * (Real.log p / Real.log N)) -
          (sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (k : ℝ) * hte)) -
            ∑ i ∈ Finset.range k, (sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + ((i : ℝ) + 1) * hte)) -
              sieveUpper306 (5.225 - 11 * ((1 / 11 : ℝ) + (i : ℝ) * hte))) *
              (if Real.log p / Real.log N < (1 / 11 : ℝ) + ((i : ℝ) + 1) * hte then (1 : ℝ) else 0))) /
          (p : ℝ))| ≤ ω * (1 / (p : ℝ)) := by
      intro p hp
      rw [abs_div, abs_of_pos (hpos p hp)]
      have h := div_le_div_of_nonneg_right (hterm p hp) (le_of_lt (hpos p hp))
      simpa [div_eq_mul_inv] using h
    refine (Finset.sum_le_sum h2).trans ?_
    rw [hS, ← Finset.mul_sum]
  -- bounds
  have hSbound : ∀ᶠ N : ℕ in atTop, S N ≤ Real.log ((1 / 3.29) / (1 / 11)) + 1 :=
    hSlimS.eventually (eventually_le_nhds (by linarith))
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (hstepB.eventually (Metric.ball_mem_nhds _ hε4))
  obtain ⟨N2, hN2⟩ := eventually_atTop.mp hdiff
  obtain ⟨N3, hN3⟩ := eventually_atTop.mp hSbound
  refine ⟨max N1 (max N2 N3), fun N hN => ?_⟩
  have hN1' : N1 ≤ N := (le_max_left _ _).trans hN
  have hN2' : N2 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN3' : N3 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hb1 := hN1 N hN1'
  have hb2 := hN2 N hN2'
  have hb3 := hN3 N hN3'
  have hAB : |A N - B N| ≤ ω * (Real.log ((1 / 3.29) / (1 / 11)) + 1) :=
    le_trans hb2 (mul_le_mul_of_nonneg_left hb3 hω0.le)
  have hB2 : |B N - L| ≤ ε / 4 := by
    simpa [Metric.mem_ball, Real.dist_eq] using hb1.le
  have hLJ : |L - J| ≤ ω * (Real.log ((1 / 3.29) / (1 / 11)) + 1) :=
    le_trans hGJ (mul_le_mul_of_nonneg_left (by linarith) hω0.le)
  have h1 : |A N - L| ≤ ω * (Real.log ((1 / 3.29) / (1 / 11)) + 1) + ε / 4 := by
    have h := abs_sub_le_add337 (A N) (B N) L
    linarith
  have h2 : |A N - J| ≤ 3 * (ε / 4) := by
    have h := abs_sub_le_add337 (A N) L J
    have hval : ω * (Real.log ((1 / 3.29) / (1 / 11)) + 1) + ε / 4 +
        ω * (Real.log ((1 / 3.29) / (1 / 11)) + 1) = 3 * (ε / 4) := by
      rw [hωL]; ring
    linarith
  rw [Real.dist_eq]
  change |A N - J| < ε
  linarith

/-- The prime weighted sum is the coefficient integral with its prefactor. -/
private theorem sieveOnePrimeSum337_eq_integral337 (N : ℕ) :
    sieveOnePrimeSum337 N = (22 * Real.exp (-Real.eulerMascheroniConstant) / 0.95) *
      (∑ p ∈ ((range (N + 1)).filter (fun p : ℕ =>
        p.Prime ∧ (N : ℝ) ^ (1 / 11 : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ (1 / 3.29 : ℝ))),
        sieveUpper306 (5.225 - 11 * (Real.log p / Real.log N)) / (p : ℝ)) := by
  unfold sieveOnePrimeSum337 z1 z2
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  have harg : (5.5 : ℝ) * 0.95 - 11 * Real.log p / Real.log N
      = 5.225 - 11 * (Real.log p / Real.log N) := by ring
  rw [harg]

/-! ### The leaf -/

/-- LEAF. Pages 601 to 602 displays 4.5 to 4.7, before prime partial summation.
The varying upper function is retained. This requires the linear sieve of Lemma 1
and the Bombieri bound of Lemma 3, including the summed recentering correction.
This is an open analytic substep, not a proved cited input. -/
theorem leaf337_one_sieve :
    ∀ δ : ℝ, 0 < δ → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (S1 N 0.95 : ℝ) ≤ (sieveOnePrimeSum337 N + δ) *
        (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
  sorry

/-- LEAF. Page 602 display 4.7, prime partial summation and evaluation of the integral.
This statement concerns only the weighted prime sum. It contains no sifted count.
The prime number theorem and the formulas of Lemma 2 give this limit. -/
theorem leaf337_one_prime_sum :
    Tendsto sieveOnePrimeSum337 atTop (𝓝 sieveOneCoefficient337) := by
  have hmain := prime_sum_limit337
  have hmul := hmain.const_mul (22 * Real.exp (-Real.eulerMascheroniConstant) / 0.95)
  have hval : (22 * Real.exp (-Real.eulerMascheroniConstant) / 0.95) *
      (∫ u in (1 / 11 : ℝ)..(1 / 3.29), sieveUpper306 (5.225 - 11 * u) / u) =
      sieveOneCoefficient337 := by
    rw [subst337a, ← coeff_eq_integral337]
  rw [← hval]
  refine Tendsto.congr' (Filter.Eventually.of_forall (fun N => ?_)) hmul
  exact (sieveOnePrimeSum337_eq_integral337 N).symm


/-- The exact sealed first upper leaf follows from the two smaller analytic steps.
CONDITIONAL ON leaf337_one_sieve and leaf337_one_prime_sum. -/
theorem sieve_one_supply337 :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (S1 N 0.95 : ℝ) ≤
        18.7347 * (C N * (N : ℝ) ^ (0.95 : ℝ) / Real.log N ^ 2) := by
  apply sieve_upper_of_limit337 (fun N => (S1 N 0.95 : ℝ)) sieveOnePrimeSum337
    sieveOneCoefficient337 18.7347
  · have h : sieveOneCoefficient337 ≤ 18.73465 := eq47_margin118
    linarith
  · exact leaf337_one_prime_sum
  · exact leaf337_one_sieve

#print axioms sieve_upper_of_limit337
#print axioms leaf337_one_sieve
#print axioms leaf337_one_prime_sum
#print axioms sieve_one_supply337

end LeanLab.Cai2002
