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
  sorry

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
