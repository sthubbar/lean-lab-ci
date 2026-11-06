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

/-- LEAF. Page 604 display 4.15, its first inequality before prime pair summation.
This is the all large count to weighted pair sum step. The source says to use
the analogous switching argument of displays 4.8 to 4.13. The cited linear sieve,
Wu 1993 https://doi.org/10.1093/qmath/44.1.109 and Huxley inputs remain open.
The mixed HuxleyDisplay413118 is insufficient for this region. -/
theorem leaf337_three_switching :
    ∀ δ : ℝ, 0 < δ → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (((switchedClosedIndex337 N (switchedThreeE306 N)).filter
        (fun b => (N - b.1 * b.2).Prime)).card : ℝ) ≤ (sieveThreePairSum337 N + δ) *
        (C N * (N : ℝ) ^ (0.95 : ℝ) / log N ^ 2) := by
  sorry

/-- LEAF. Page 604 display 4.15, the all large prime pair sum to its integral.
This has no S3 count and no switched remainder. The order p1 less than p2
is retained. Coprimality with N permits an upper limit with every reserve. -/
theorem leaf337_three_pair_sum :
    ∀ δ : ℝ, 0 < δ → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      sieveThreePairSum337 N ≤ sieveThreeCoefficient337 + δ := by
  sorry

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
