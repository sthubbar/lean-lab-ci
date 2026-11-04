/- AI wrote this Lean code for CODEX task169.
Theorem 5, journal pp. 1228 to 1231. Goldbach is open. -/
import LeanLab.BS2022GRH.Decomp138
import LeanLab.BS2022GRH.DecompC164a
import LeanLab.BS2022GRH.EndpointC169
import LeanLab.BS2022GRH.DecompC169c
import LeanLab.BS2022GRH.PublishedInputs233
import LeanLab.BS2022GRH.ModelC233
import LeanLab.BS2022GRH.RemainderC233
import LeanLab.BS2022GRH.PublishedInputs232
import LeanLab.BS2022GRH.Verify1565

namespace LeanLab.BS2022GRH.DecompC169a
open Real Finset Classical ChenThresholdGRH
noncomputable section

/-- A lower level preserves the finite prime set, journal p. 1229.
The extra lower bound lets the sieve parameter stay below four. -/
theorem lower_level_same_primes (n : ℕ) (b z : ℝ) (hb : b < z) :
    ∃ z₁, b < z₁ ∧ z₁ < z ∧ primesBelow n z₁ = primesBelow n z := by
  let s := primesBelow n z
  have htop : ∀ p ∈ s, (p : ℝ) < z := fun p hp => (mem_filter.mp hp).2.2.2
  have hbound : ∃ c, b ≤ c ∧ c < z ∧ ∀ p ∈ s, (p : ℝ) ≤ c := by
    by_cases hs : s.Nonempty
    · obtain ⟨p, hp, hmax⟩ := s.exists_max_image (fun p => (p : ℝ)) hs
      exact ⟨max b p, le_max_left _ _, max_lt hb (htop p hp),
        fun q hq => (hmax q hq).trans (le_max_right _ _)⟩
    · exact ⟨b, le_rfl, hb, fun p hp => False.elim (hs ⟨p, hp⟩)⟩
  obtain ⟨c, hbc, hcz, hc⟩ := hbound
  obtain ⟨z₁, hcz₁, hz₁z⟩ := exists_between hcz
  refine ⟨z₁, hbc.trans_lt hcz₁, hz₁z, ?_⟩
  ext p
  constructor
  · intro hp
    obtain ⟨_, hprime, hpn, hpz₁⟩ := mem_filter.mp hp
    have hpz := hpz₁.trans hz₁z
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_ceil.mpr hpz), hprime, hpn, hpz⟩
  · intro hp
    obtain ⟨_, hprime, hpn, _⟩ := mem_filter.mp hp
    have hpz₁ : (p : ℝ) < z₁ := (hc p hp).trans_lt hcz₁
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_ceil.mpr hpz₁), hprime, hpn, hpz₁⟩

/-- Every density factor is positive for even n, journal p. 1229. -/
theorem density_pos (n : ℕ) (hev : Even n) : 0 < density n := by
  apply prod_pos
  intro p hp
  obtain ⟨_, hprime, hpn, _⟩ := mem_filter.mp hp
  have hp3 : 3 ≤ p := by
    have hp2 := hprime.two_le
    have hne : p ≠ 2 := fun h => hpn (h ▸ hev.two_dvd)
    omega
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hlt : (1 : ℝ) / (p - 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  linarith

/-- A prime factor of n minus one supplies a member of A, journal p. 1227. -/
theorem aset_card_pos (n : ℕ) (hn : 3 ≤ n) : 0 < (U7153.Aset n).card := by
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show n - 1 ≠ 1 by omega)
  have hpn : ¬ p ∣ n := by
    intro h
    have h1 : p ∣ 1 := by
      have heq : n - (n - 1) = 1 := by omega
      rw [← heq]
      exact Nat.dvd_sub h hpd
    exact hp.not_dvd_one h1
  have hple := Nat.le_of_dvd (show 0 < n - 1 by omega) hpd
  apply card_pos.mpr
  refine ⟨n - p, mem_image.mpr ⟨p, ?_, rfl⟩⟩
  exact mem_filter.mpr ⟨mem_range.mpr (by omega), hp, hpn⟩

/-- The logarithmic part of f is strictly increasing from three to four, p. 1218. -/
theorem log_ratio_strictMono :
    StrictMonoOn (fun s : ℝ => log (s - 1) / s) (Set.Icc 3 4) := by
  have hlog3 : log (3 : ℝ) < 6 / 5 := by
    rw [log_lt_iff_lt_exp (by norm_num)]
    have h := add_one_le_exp (1 / 5 : ℝ)
    have he : exp (6 / 5 : ℝ) = exp 1 * exp (1 / 5) := by
      rw [← exp_add]; congr 1; norm_num
    rw [he]
    nlinarith [exp_one_gt_d9]
  have hd (s : ℝ) (hs : s ∈ Set.Icc (3 : ℝ) 4) :
      HasDerivAt (fun t : ℝ => log (t - 1) / t)
        ((s / (s - 1) - log (s - 1)) / s ^ 2) s := by
    obtain ⟨hs3, hs4⟩ := hs
    have h := (((hasDerivAt_id s).sub_const 1).log (by linarith : s - 1 ≠ 0)).div
      (hasDerivAt_id s) (by linarith : s ≠ 0)
    convert h using 1
    · ext t
      rfl
    · dsimp
      ring
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · intro s hs
    exact (hd s hs).continuousAt.continuousWithinAt
  · intro s hs
    have hs' : s ∈ Set.Icc (3 : ℝ) 4 := interior_subset hs
    rw [(hd s hs').deriv]
    obtain ⟨hs3, hs4⟩ := hs'
    have hlog : log (s - 1) < 6 / 5 :=
      (log_le_log (by linarith) (by linarith : s - 1 ≤ 3)).trans_lt hlog3
    have hrat : (4 / 3 : ℝ) ≤ s / (s - 1) := by
      rw [le_div_iff₀ (by linarith : 0 < s - 1)]
      linarith
    exact div_pos (by linarith) (by positivity)

/-- The h term decreases on the branch used by Theorem 5, p. 1229. -/
theorem hS_antitone_three (s t : ℝ) (hs : 3 ≤ s) (hst : s ≤ t) : hS t ≤ hS s := by
  have heq (x : ℝ) (hx : 3 ≤ x) : hS x = 3 / x * exp (-x) := by
    by_cases h : x ≤ 3
    · have hx3 : x = 3 := by linarith
      subst x
      norm_num [hS]
    · simp [hS, show ¬ x ≤ 2 by linarith, h]
  rw [heq s hs, heq t (hs.trans hst)]
  exact mul_le_mul (div_le_div_of_nonneg_left (by norm_num) (by linarith) hst)
    (exp_le_exp.mpr (by linarith)) (exp_pos _).le (by positivity)

/-- Strict coefficient gain at a larger s, journal p. 1229. -/
theorem lower_sieve_coefficient_strict (s t ε C₂ : ℝ)
    (hs : 3 ≤ s) (hst : s < t) (ht : t ≤ 4) (he : 0 ≤ ε) (hC : 0 ≤ C₂) :
    2 * exp eulerMascheroniConstant * log (s - 1) / s - ε * C₂ * exp 2 * hS s <
      2 * exp eulerMascheroniConstant * log (t - 1) / t - ε * C₂ * exp 2 * hS t := by
  have hf := log_ratio_strictMono ⟨hs, by linarith⟩ ⟨by linarith, ht⟩ hst
  have hf' := mul_lt_mul_of_pos_left hf (by positivity : 0 < 2 * exp eulerMascheroniConstant)
  have hh := mul_le_mul_of_nonneg_left (hS_antitone_three s t hs hst.le)
    (show 0 ≤ ε * C₂ * exp 2 by positivity)
  dsimp only at hf'
  simp only [← mul_div_assoc] at hf'
  linarith

/-- The generic sieve prime set equals the concrete set, journal p. 1229. -/
theorem lower_prime_set (n : ℕ) (z : ℝ) :
    @Finset.filter ℕ (fun p => p ∈ ({p : ℕ | p.Prime ∧ ¬ p ∣ n} : Set ℕ) ∧
      (p : ℝ) < z)
      (fun p => @instDecidableAnd _ _ (Classical.propDecidable _) (by infer_instance))
      (range ⌈z⌉₊) = primesBelow n z := by
  ext p
  simp [primesBelow, and_assoc]

/-- The sifted indicator sum is exactly SA, journal p. 1229.
This repeats the specialization of SieveModelC169 without a circular import. -/
theorem lower_sifted_sum (n : ℕ) :
    (∑ m ∈ (U7153.Aset n).filter
      (fun m => ∀ p ∈ primesBelow n (U7153.zz n), ¬ p ∣ m),
      if m ∈ U7153.Aset n then (1 : ℝ) else 0) = (U7153.SA n : ℝ) := by
  have hpred (m : ℕ) :
      (∀ p ∈ primesBelow n (U7153.zz n), ¬ p ∣ m) ↔
        U7153.NoSmallP n (U7153.zz n) m := by
    constructor
    · intro h p hp hpz hpn
      exact h p (mem_filter.mpr
        ⟨mem_range.mpr (Nat.lt_ceil.mpr hpz), hp, hpn, hpz⟩)
    · intro h p hp
      obtain ⟨_, hp, hpn, hpz⟩ := mem_filter.mp hp
      exact h p hp hpz hpn
  simp_rw [hpred]
  calc
    _ = ∑ m ∈ (U7153.Aset n).filter (U7153.NoSmallP n (U7153.zz n)), (1 : ℝ) := by
      apply sum_congr rfl
      intro m hm
      rw [if_pos (mem_filter.mp hm).1]
    _ = _ := by simp [U7153.SA]

/-- The generic main mass is V times cardinality, journal p. 1229. -/
theorem lower_main_mass (n : ℕ) :
    (∑ m ∈ U7153.Aset n, (if m ∈ U7153.Aset n then (1 : ℝ) else 0) *
      ∏ p ∈ primesBelow n (U7153.zz n), (1 - 1 / ((p : ℝ) - 1))) =
        density n * ((U7153.Aset n).card : ℝ) := by
  simp [density, mul_comm]

/-- The squarefree density is reciprocal totient, journal p. 1229. -/
theorem lower_squarefree_model (d : ℕ) (hd : Squarefree d) :
    (∏ p ∈ d.primeFactors, (1 : ℝ) / ((p : ℝ) - 1)) = 1 / (d.totient : ℝ) := by
  have hφ : d.totient = ∏ p ∈ d.primeFactors, (p - 1) := by
    rw [Nat.totient_eq_div_primeFactors_mul, Nat.prod_primeFactors_of_squarefree hd,
      Nat.div_self (Nat.pos_of_ne_zero hd.ne_zero), one_mul]
  have hφR : (d.totient : ℝ) = ∏ p ∈ d.primeFactors, ((p : ℝ) - 1) := by
    rw [hφ, Nat.cast_prod]
    apply prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  simp_rw [one_div]
  rw [prod_inv_distrib, ← hφR]

/-- The generic divisor error is exactly r, journal p. 1229. -/
theorem lower_divisor_error (n d : ℕ) (hd : Squarefree d) :
    (∑ m ∈ (U7153.Aset n).filter (fun m => d ∣ m),
      if m ∈ U7153.Aset n then (1 : ℝ) else 0) -
      (∑ m ∈ U7153.Aset n, (if m ∈ U7153.Aset n then (1 : ℝ) else 0) *
        ∏ p ∈ d.primeFactors, (1 / ((p : ℝ) - 1))) = residue n d := by
  rw [lower_squarefree_model d hd]
  have hsum : (∑ m ∈ (U7153.Aset n).filter (fun m => d ∣ m),
      if m ∈ U7153.Aset n then (1 : ℝ) else 0) =
        (((U7153.Aset n).filter (fun m => d ∣ m)).card : ℝ) := by
    calc
      _ = ∑ _m ∈ (U7153.Aset n).filter (fun m => d ∣ m), (1 : ℝ) := by
        apply sum_congr rfl
        intro m hm
        rw [if_pos (mem_filter.mp hm).1]
      _ = _ := by simp
  rw [hsum]
  simp [residue, div_eq_mul_inv]

/-- Prime subsets and squarefree divisor images give the same error sum, p. 1229. -/
theorem lower_remainder_sum (n : ℕ) (α u : ℝ) :
    (∑ T ∈ (primesBelow n (U7153.zz n)).powerset.filter
      (fun T => ((∏ p ∈ T, p : ℕ) : ℝ) <
        (∏ p ∈ primesBelow n u, p : ℕ) * (n : ℝ) ^ (1 / 2 - α)),
      |(∑ m ∈ (U7153.Aset n).filter (fun m => (∏ p ∈ T, p) ∣ m),
          if m ∈ U7153.Aset n then (1 : ℝ) else 0) -
        ∑ m ∈ U7153.Aset n, (if m ∈ U7153.Aset n then (1 : ℝ) else 0) *
          ∏ p ∈ (∏ p ∈ T, p).primeFactors, (1 / ((p : ℝ) - 1))|) =
      remainder n α u := by
  have hprime (T : Finset ℕ) (hT : T ∈ (primesBelow n (U7153.zz n)).powerset) :
      ∀ p ∈ T, Nat.Prime p := fun p hp =>
    (mem_filter.mp (mem_powerset.mp hT hp)).2.1
  symm
  unfold remainder sieveDivisors smallProduct
  rw [sum_filter, sum_image]
  · rw [← sum_filter]
    apply sum_congr rfl
    intro T hT
    have hp := hprime T (mem_filter.mp hT).1
    have hsq : Squarefree (∏ p ∈ T, p) := by
      apply Finset.squarefree_prod_of_pairwise_isCoprime
      · intro p hpT q hqT hpq
        exact Nat.coprime_iff_isRelPrime.mp
          ((Nat.coprime_primes (hp p hpT) (hp q hqT)).mpr hpq)
      · intro p hpT
        exact (hp p hpT).squarefree
    rw [lower_divisor_error n (∏ p ∈ T, p) hsq]
  · intro T hT T' hT' heq
    have h1 := Nat.primeFactors_prod (hprime T hT)
    have h2 := Nat.primeFactors_prod (hprime T' hT')
    exact h1.symm.trans ((congrArg Nat.primeFactors heq).trans h2)

/-- A prime band estimate gives the product guard of Theorem 4, p. 1229. -/
theorem lower_product_guard (n : ℕ) (u ε z : ℝ)
    (hu : 400 ≤ u) (hz : 1 < z) (he : 0 ≤ ε) (heps : epsJ u ≤ ε)
    (hband : ∀ v, u ≤ v → v < z →
      (∏ p ∈ (range ⌈z⌉₊).filter
        (fun p : ℕ => p.Prime ∧ v ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - 1 / ((p : ℝ) - 1))⁻¹) < (1 + epsJ u) * (log z / log v)) :
    ∀ v, 1 < v → v < z →
      (∏ p ∈ (range ⌈z⌉₊).filter
        (fun p => p ∈ ({p : ℕ | p.Prime ∧ ¬ p ∣ n} : Set ℕ) ∧
          p ∉ primesBelow n u ∧ v ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤ (1 + ε) * (log z / log v) := by
  intro v hv hvz
  let F := (range ⌈z⌉₊).filter
    (fun p => p ∈ ({p : ℕ | p.Prime ∧ ¬ p ∣ n} : Set ℕ) ∧
      p ∉ primesBelow n u ∧ v ≤ (p : ℝ) ∧ (p : ℝ) < z)
  have hpu (p : ℕ) (hp : p ∈ F) : u ≤ (p : ℝ) := by
    obtain ⟨_, hpP, hpQ, _, _⟩ := mem_filter.mp hp
    by_contra h
    have hlt : (p : ℝ) < u := lt_of_not_ge h
    exact hpQ (mem_filter.mpr ⟨mem_range.mpr (Nat.lt_ceil.mpr hlt), hpP.1, hpP.2, hlt⟩)
  have hlogv : 0 < log v := log_pos hv
  have hlogz : 0 < log z := log_pos hz
  have hratio : 1 ≤ log z / log v :=
    (le_div_iff₀ hlogv).mpr (by simpa using (log_lt_log (by linarith) hvz).le)
  by_cases huz : u < z
  · let w := max v u
    let B := (range ⌈z⌉₊).filter
      (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z)
    have hwz : w < z := max_lt hvz huz
    have hwu : u ≤ w := le_max_right _ _
    have hsub : F ⊆ B := by
      intro p hp
      obtain ⟨hpR, hpP, _, hpv, hpz⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨hpR, hpP.1, max_le hpv (hpu p hp), hpz⟩
    have hone (p : ℕ) (hp : p ∈ B) : 1 ≤ (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
      have hpw := (mem_filter.mp hp).2.2.1
      have hp400 : (400 : ℝ) ≤ p := hu.trans (hwu.trans hpw)
      have hpos : 0 < 1 - 1 / ((p : ℝ) - 1) := by
        have hlt : (1 : ℝ) / (p - 1) < 1 :=
          (div_lt_one (by linarith)).mpr (by linarith)
        linarith
      exact (one_le_inv₀ hpos).mpr (by
        have hnn : 0 ≤ (1 : ℝ) / (p - 1) := div_nonneg (by norm_num) (by linarith)
        linarith)
    have hprod : ∏ p ∈ F, (1 - 1 / ((p : ℝ) - 1))⁻¹ ≤
        ∏ p ∈ B, (1 - 1 / ((p : ℝ) - 1))⁻¹ :=
      prod_le_prod_of_subset_of_one_le₀ hsub
        (fun p hp => (zero_le_one.trans (hone p (hsub hp)))) (fun p hp _ => hone p hp)
    have hlogw : 0 < log w := log_pos (hv.trans_le (le_max_left _ _))
    have hdiv : log z / log w ≤ log z / log v :=
      div_le_div_of_nonneg_left hlogz.le hlogv (log_le_log (by linarith) (le_max_left _ _))
    exact hprod.trans ((hband w hwu hwz).le.trans
      (mul_le_mul (by linarith) hdiv (by positivity) (by linarith)))
  · have hF : F = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hpz := (mem_filter.mp hp).2.2.2.2
      have hpU := hpu p hp
      linarith
    change (∏ p ∈ F, _) ≤ _
    rw [hF, prod_empty]
    exact hratio.trans (le_mul_of_one_le_left (by positivity) (by linarith))

/-- The coefficient at the unshifted level is the displayed coefficient, p. 1229. -/
theorem lower_coefficient_at_parameter (α ε C₂ : ℝ) (hα : α < 1 / 8) :
    2 * exp eulerMascheroniConstant * log ((4 - 8 * α) - 1) / (4 - 8 * α) -
      ε * C₂ * exp 2 * hS (4 - 8 * α) = lowerCoefficient α ε C₂ := by
  have hs : 3 < 4 - 8 * α := by linarith
  have he : exp 2 * exp (-(4 - 8 * α)) = exp (8 * α - 2) := by
    rw [← exp_add]
    congr 1
    ring
  simp only [hS, if_neg (by linarith : ¬ 4 - 8 * α ≤ 2), if_neg hs.not_ge]
  unfold lowerCoefficient
  rw [show 4 - 8 * α - 1 = 3 - 8 * α by ring]
  calc
    _ = 2 * exp eulerMascheroniConstant * log (3 - 8 * α) / (4 - 8 * α) -
      ε * C₂ * (3 / (4 - 8 * α) * (exp 2 * exp (-(4 - 8 * α)))) := by ring
    _ = _ := by rw [he]; ring

/-- A band estimate only above a chosen floor gives strictness, journal p. 1229.
The floor is below the original level and at least exp 400. -/
theorem sieve_lower_of_band_above (α u ε C₁ C₂ : ℝ) (n : ℕ) (z₀ : ℝ)
    (hT : LinearSieveT4 ε C₁ C₂) (hC₂ : 0 ≤ C₂)
    (heps : epsJ u ≤ ε) (he0 : 0 < ε) (he1 : ε < 1 / 63)
    (hα : 0 < α) (hα1 : α < 1 / 8) (hu : 400 ≤ u)
    (hnlog : 3200 < log (n : ℝ)) (hev : Even n)
    (hz₀ : exp 400 ≤ z₀) (hz₀n : z₀ < U7153.zz n)
    (hband : ∀ z v, z₀ < z → u ≤ v → v < z →
      (∏ p ∈ (range ⌈z⌉₊).filter
        (fun p : ℕ => p.Prime ∧ v ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - 1 / ((p : ℝ) - 1))⁻¹) < (1 + epsJ u) * (log z / log v)) :
    sieveMain n α ε C₂ - remainder n α u < (U7153.SA n : ℝ) := by
  have hn1 : (1 : ℝ) < n := (log_pos_iff (Nat.cast_nonneg n)).mp (by linarith)
  have hn0 : (0 : ℝ) < n := by linarith
  have hn3 : 3 ≤ n := by
    by_contra h
    have hnle : (n : ℝ) ≤ 2 := by exact_mod_cast (show n ≤ 2 by omega)
    have hlogle := log_le_log hn0 hnle
    have hl2 := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  let z := U7153.zz n
  let D := (n : ℝ) ^ (1 / 2 - α)
  have hz0 : 0 < z := rpow_pos_of_pos hn0 _
  have hD0 : 0 < D := rpow_pos_of_pos hn0 _
  have hlz : log z = (1 / 8 : ℝ) * log (n : ℝ) := log_rpow hn0 _
  have hlD : log D = (1 / 2 - α) * log (n : ℝ) := log_rpow hn0 _
  have hlz400 : 400 < log z := by rw [hlz]; linarith
  have hlD0 : 0 < log D := by rw [hlD]; exact mul_pos (by linarith) (by linarith)
  have hs0 : log D / log z = 4 - 8 * α := by
    rw [hlD, hlz]
    field_simp
    <;> ring
  have hquart : log D / 4 < log z := by
    rw [hlD, hlz]
    nlinarith
  have hb : max z₀ (exp (log D / 4)) < z := by
    apply max_lt hz₀n
    change exp (log D / 4) < z
    rw [← exp_log hz0]
    exact exp_lt_exp.mpr hquart
  obtain ⟨z₁, hbz₁, hz₁z, hsame⟩ := lower_level_same_primes n _ z hb
  have hz₁floor : z₀ < z₁ := (le_max_left _ _).trans_lt hbz₁
  have hz₁400 : exp 400 < z₁ := hz₀.trans_lt hz₁floor
  have hz₁quart : exp (log D / 4) < z₁ := (le_max_right _ _).trans_lt hbz₁
  have hz₁0 : 0 < z₁ := (exp_pos 400).trans hz₁400
  have hz₁1 : 1 < z₁ := (one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 400)).trans hz₁400
  have hz₁2 : 2 ≤ z₁ := by
    have he := add_one_le_exp (400 : ℝ)
    linarith
  have hlz₁0 : 0 < log z₁ := log_pos hz₁1
  have hlz₁z : log z₁ < log z := log_lt_log hz₁0 hz₁z
  have hlz₁quart : log D / 4 < log z₁ := by
    have h := log_lt_log (exp_pos _) hz₁quart
    simpa only [log_exp] using h
  let s₁ := log D / log z₁
  have hss₁ : 4 - 8 * α < s₁ := by
    rw [← hs0]
    exact div_lt_div_of_pos_left hlD0 hlz₁0 hlz₁z
  have hs₁4 : s₁ ≤ 4 := by
    apply (div_le_iff₀ hlz₁0).mpr
    linarith
  have hzD : z₁ ^ 2 ≤ D := by
    apply (log_le_log_iff (pow_pos hz₁0 2) hD0).mp
    rw [log_pow]
    norm_num
    have hs3 : 3 < log D / log z₁ := by linarith
    have hmul := (lt_div_iff₀ hlz₁0).mp hs3
    linarith
  have hprod := lower_product_guard n u ε z₁ hu hz₁1 he0.le heps
    (fun v huv hvz => hband z₁ v hz₁floor huv hvz)
  have hg : ∀ x : ℕ, ∀ p ∈ ({p : ℕ | p.Prime ∧ ¬ p ∣ n} : Set ℕ),
      0 ≤ 1 / ((p : ℝ) - 1) ∧ 1 / ((p : ℝ) - 1) < 1 := by
    intro x p hp
    have hp3 : 3 ≤ p := by
      have hp2 := hp.1.two_le
      have hne : p ≠ 2 := fun h => hp.2 (h ▸ hev.two_dvd)
      omega
    have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    exact ⟨div_nonneg (by norm_num) (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩
  have hQ : (↑(primesBelow n u) : Set ℕ) ⊆ {p : ℕ | p.Prime ∧ ¬ p ∣ n} := by
    intro p hp
    exact ⟨(mem_filter.mp hp).2.1, (mem_filter.mp hp).2.2.1⟩
  have key := hT (U7153.Aset n) (fun m => if m ∈ U7153.Aset n then (1 : ℝ) else 0)
    {p : ℕ | p.Prime ∧ ¬ p ∣ n} (primesBelow n u) (fun _ p => 1 / ((p : ℝ) - 1)) z₁ D
    (by intro m; split_ifs <;> norm_num) (by intro m hm; simp [hm])
    (fun _ hp => hp.1) hQ hg he0 he1 hz₁2 (fun _ v hv hvz => by
      convert hprod v hv hvz using 1 <;> congr 1 <;> ext p <;> simp)
  have hmain := key.2 hzD hs₁4
  simp only [filter_congr_decidable] at hmain
  rw [lower_prime_set n z₁, hsame, lower_sifted_sum n, lower_main_mass n,
    lower_remainder_sum n α u] at hmain
  have hcoef : lowerCoefficient α ε C₂ <
      2 * exp eulerMascheroniConstant * log (s₁ - 1) / s₁ - ε * C₂ * exp 2 * hS s₁ := by
    rw [← lower_coefficient_at_parameter α ε C₂ hα1]
    exact lower_sieve_coefficient_strict _ _ ε C₂ (by linarith) hss₁ hs₁4 he0.le hC₂
  have hmass : 0 < density n * ((U7153.Aset n).card : ℝ) :=
    mul_pos (density_pos n hev) (by exact_mod_cast aset_card_pos n hn3)
  have hstrict := mul_lt_mul_of_pos_right hcoef hmass
  unfold sieveMain
  dsimp only [s₁] at hstrict
  nlinarith

/-- Strictness from a nearby lower level with the same primes, journal p. 1229.
CONDITIONAL ON the sieve and the explicit band product hypothesis. -/
theorem sieve_lower_of_band (α u ε C₁ C₂ : ℝ) (n : ℕ)
    (hT : LinearSieveT4 ε C₁ C₂) (hC₂ : 0 ≤ C₂)
    (heps : epsJ u ≤ ε) (he0 : 0 < ε) (he1 : ε < 1 / 63)
    (hα : 0 < α) (hα1 : α < 1 / 8) (hu : 400 ≤ u)
    (hnlog : 3200 < log (n : ℝ)) (hev : Even n)
    (hband : ∀ z v, exp 400 < z → u ≤ v → v < z →
      (∏ p ∈ (range ⌈z⌉₊).filter
        (fun p : ℕ => p.Prime ∧ v ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - 1 / ((p : ℝ) - 1))⁻¹) < (1 + epsJ u) * (log z / log v)) :
    sieveMain n α ε C₂ - remainder n α u < (U7153.SA n : ℝ) := by
  have hn1 : (1 : ℝ) < n := (log_pos_iff (Nat.cast_nonneg n)).mp (by linarith)
  have hn0 : (0 : ℝ) < n := by linarith
  have hz0 : 0 < U7153.zz n := rpow_pos_of_pos hn0 _
  have hzfloor : exp 400 < U7153.zz n := by
    rw [← exp_log hz0]
    apply exp_lt_exp.mpr
    rw [U7153.zz, log_rpow hn0]
    linarith
  exact sieve_lower_of_band_above α u ε C₁ C₂ n (exp 400) hT hC₂ heps he0 he1
    hα hα1 hu hnlog hev le_rfl hzfloor hband

/-- The strict lower sieve on the range covered by Lemma 7, journal p. 1229.
CONDITIONAL ON LinearSieveT4 and Lemma7J, with no small-level input. -/
theorem sieve_lower_large (α u ε C₁ C₂ : ℝ) (n : ℕ)
    (hT : LinearSieveT4 ε C₁ C₂) (hL : Lemma7J) (hC₂ : 0 ≤ C₂)
    (heps : epsJ u ≤ ε) (he0 : 0 < ε) (he1 : ε < 1 / 63)
    (hα : 0 < α) (hα1 : α < 1 / 8) (hu : 400 ≤ u)
    (hnlog : 3200 < log (n : ℝ)) (hev : Even n) (hz : exp 2753 < U7153.zz n) :
    sieveMain n α ε C₂ - remainder n α u < (U7153.SA n : ℝ) := by
  apply sieve_lower_of_band_above α u ε C₁ C₂ n (exp 2753) hT hC₂ heps he0 he1
    hα hα1 hu hnlog hev (exp_le_exp.mpr (by norm_num)) hz
  intro z v hz huv hvz
  exact (hL z u v hz hu huv hvz).1

/-- The journal's exp exp ten threshold lies in the large-level source range, p. 1228. -/
theorem lower_large_level_guard (n : ℕ) (hn : exp (exp 10) ≤ (n : ℝ)) :
    3200 < log (n : ℝ) ∧ exp 2753 < U7153.zz n := by
  have hn0 : (0 : ℝ) < n := (exp_pos _).trans_le hn
  have hL : exp 10 ≤ log (n : ℝ) := (le_log_iff_exp_le hn0).mpr hn
  have he : (22024 : ℝ) < exp 10 := by
    have h := exp_nat_ge 10
    norm_num at h
    norm_num
    linarith
  constructor
  · linarith
  · have hz0 : 0 < U7153.zz n := rpow_pos_of_pos hn0 _
    rw [← exp_log hz0]
    apply exp_lt_exp.mpr
    rw [U7153.zz, log_rpow hn0]
    linarith

/-- A concrete nonempty elementary domain for the strict lower sieve, p. 1229.
GRH and the two cited sieve inputs are not asserted by this instance. -/
theorem lower_sieve_domain_instance :
    ∃ n : ℕ, Even n ∧ exp (exp 13.375) ≤ (n : ℝ) ∧
      3200 < log (n : ℝ) ∧ exp 2753 < U7153.zz n ∧
      0 < density n ∧ 0 < (U7153.Aset n).card := by
  obtain ⟨n, hev, hn⟩ := threshold_nonvacuous
  have hlarge := lower_large_level_guard n (X2_ranges.2.trans hn)
  have hn3 : 3 ≤ n := by
    have hN := X2_ranges.1.trans hn
    exact_mod_cast (show (3 : ℝ) ≤ n by linarith)
  exact ⟨n, hev, hn, hlarge.1, hlarge.2, density_pos n hev, aset_card_pos n hn3⟩

/-- The finite density splits into the Mertens and twin factors, p. 1227. -/
theorem density_euler_split (n : ℕ) (hev : Even n) :
    density n = (∏ p ∈ primesBelow n (U7153.zz n), (1 - 1 / (p : ℝ))) *
      ∏ p ∈ primesBelow n (U7153.zz n), (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  apply Verify1565.prod_identity
  intro p hp
  obtain ⟨_, hprime, hpn, _⟩ := mem_filter.mp hp
  have hne : p ≠ 2 := fun h => hpn (h ▸ hev.two_dvd)
  have hp2 := hprime.two_le
  omega

/-- A finite product over odd primes is at least the twin constant, p. 1227. -/
theorem twin_constant_le_finite (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime ∧ 2 < p) :
    LeanLab.ChenExplicit.twinC ≤ ∏ p ∈ T, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  have hnonpos (n : ℕ) : LeanLab.ChenExplicit.aT n ≤ 0 := by
    unfold LeanLab.ChenExplicit.aT
    split_ifs with hn
    · apply log_nonpos (LeanLab.ChenExplicit.gT_pos hn.2).le
      unfold LeanLab.ChenExplicit.gT
      have hnn : 0 ≤ (1 : ℝ) / ((n : ℝ) - 1) ^ 2 := by positivity
      linarith
    · exact le_rfl
  have hsum := LeanLab.ChenExplicit.summable_aT.neg.sum_le_tsum T
    (fun n _ => neg_nonneg.mpr (hnonpos n))
  rw [sum_neg_distrib, tsum_neg] at hsum
  have hsum' : (∑' n, LeanLab.ChenExplicit.aT n) ≤ ∑ n ∈ T, LeanLab.ChenExplicit.aT n := by
    linarith
  rw [LeanLab.ChenExplicit.twinC_eq_exp]
  apply (exp_le_exp.mpr hsum').trans_eq
  rw [exp_sum]
  apply prod_congr rfl
  intro p hp
  rw [LeanLab.ChenExplicit.aT, if_pos (hT p hp),
    exp_log (LeanLab.ChenExplicit.gT_pos (hT p hp).2)]
  rfl

/-- The factor two from excluding prime two is exact, journal Lemma 10 p. 1227.
The remaining finite product is the ordinary Mertens product on eligible primes. -/
theorem density_mertens_lower (n : ℕ) (hev : Even n) :
    2 * LeanLab.ChenExplicit.twinC *
      (∏ p ∈ insert 2 (primesBelow n (U7153.zz n)), (1 - 1 / (p : ℝ))) ≤ density n := by
  have h2 : 2 ∉ primesBelow n (U7153.zz n) := by
    intro h
    exact (mem_filter.mp h).2.2.1 hev.two_dvd
  have hodd (p : ℕ) (hp : p ∈ primesBelow n (U7153.zz n)) : p.Prime ∧ 2 < p := by
    obtain ⟨_, hprime, hpn, _⟩ := mem_filter.mp hp
    have hne : p ≠ 2 := fun h => hpn (h ▸ hev.two_dvd)
    exact ⟨hprime, by have := hprime.two_le; omega⟩
  have ht := twin_constant_le_finite (primesBelow n (U7153.zz n)) hodd
  have hp0 : 0 ≤ ∏ p ∈ primesBelow n (U7153.zz n), (1 - 1 / (p : ℝ)) := by
    apply prod_nonneg
    intro p hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (hodd p hp).2
    have hdiv : (1 : ℝ) / p ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    linarith
  have hm := mul_le_mul_of_nonneg_left ht hp0
  rw [prod_insert h2, show (1 - 1 / ((2 : ℕ) : ℝ)) = (1 / 2 : ℝ) by norm_num,
    density_euler_split n hev]
  nlinarith

/-- The finite product lower bound used for the divisor correction, p. 1227. -/
theorem finite_prod_one_sub_lower (s : Finset ℕ) (f : ℕ → ℝ)
    (hf0 : ∀ p ∈ s, 0 ≤ f p) (hf1 : ∀ p ∈ s, f p ≤ 1) :
    1 - ∑ p ∈ s, f p ≤ ∏ p ∈ s, (1 - f p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
    have hp0 := hf0 p (mem_insert_self _ _)
    have hp1 := hf1 p (mem_insert_self _ _)
    have hs0 := fun q hq => hf0 q (mem_insert_of_mem hq)
    have hs1 := fun q hq => hf1 q (mem_insert_of_mem hq)
    have htail := ih hs0 hs1
    have hprod : ∏ q ∈ s, (1 - f q) ≤ 1 :=
      prod_le_one₀ (fun q hq => by linarith [hs1 q hq])
        (fun q hq => by linarith [hs0 q hq])
    have hm := mul_le_mul_of_nonneg_left hprod hp0
    rw [sum_insert hps, prod_insert hps]
    nlinarith

/-- The number of distinct prime divisors is at most twice log n, p. 1227.
This coarse elementary bound suffices for the large prime-divisor correction. -/
theorem prime_factor_card_le_two_log (n : ℕ) (hn : 0 < n) :
    (n.primeFactors.card : ℝ) ≤ 2 * log (n : ℝ) := by
  have hpow : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
    rw [← prod_const]
    exact prod_le_prod fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hprod : (∏ p ∈ n.primeFactors, p) ≤ n :=
    Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  have hpowR : (2 : ℝ) ^ n.primeFactors.card ≤ n := by exact_mod_cast hpow.trans hprod
  have hlog := log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpowR
  rw [log_pow] at hlog
  have hlog2 : (1 / 2 : ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
  have hcard0 : (0 : ℝ) ≤ n.primeFactors.card := Nat.cast_nonneg _
  nlinarith

/-- Large prime divisors cost at most four log n over z in the product, p. 1227. -/
theorem large_prime_divisor_product (n : ℕ) (z : ℝ) (hn : 0 < n) (hz : 3 ≤ z) :
    1 - 4 * log (n : ℝ) / z ≤
      ∏ p ∈ n.primeFactors.filter (fun p : ℕ => z ≤ (p : ℝ)), (1 - 1 / ((p : ℝ) - 1)) := by
  let T : Finset ℕ := n.primeFactors.filter (fun p : ℕ => z ≤ (p : ℝ))
  have hp3 (p : ℕ) (hp : p ∈ T) : (3 : ℝ) ≤ p := hz.trans (mem_filter.mp hp).2
  have hf0 (p : ℕ) (hp : p ∈ T) : 0 ≤ (1 : ℝ) / (p - 1) :=
    div_nonneg (by norm_num) (by linarith [hp3 p hp])
  have hf1 (p : ℕ) (hp : p ∈ T) : (1 : ℝ) / (p - 1) ≤ 1 :=
    (div_le_one (by linarith [hp3 p hp])).mpr (by linarith [hp3 p hp])
  have hsmall (p : ℕ) (hp : p ∈ T) : (1 : ℝ) / (p - 1) ≤ 2 / z := by
    rw [div_le_div_iff₀ (by linarith [hp3 p hp]) (by linarith : 0 < z)]
    have hzp := (mem_filter.mp hp).2
    linarith [hp3 p hp]
  have hcard : (T.card : ℝ) ≤ n.primeFactors.card := by
    exact_mod_cast card_filter_le n.primeFactors (fun p => z ≤ (p : ℝ))
  have hsum : (∑ p ∈ T, (1 : ℝ) / (p - 1)) ≤ 4 * log (n : ℝ) / z := by
    calc
      _ ≤ ∑ _p ∈ T, (2 / z : ℝ) := sum_le_sum hsmall
      _ = (T.card : ℝ) * (2 / z) := by simp
      _ ≤ (n.primeFactors.card : ℝ) * (2 / z) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ (2 * log (n : ℝ)) * (2 / z) :=
        mul_le_mul_of_nonneg_right (prime_factor_card_le_two_log n hn) (by positivity)
      _ = _ := by ring
  exact (sub_le_sub_left hsum 1).trans (finite_prod_one_sub_lower T _ hf0 hf1)

/-- Transferring only from a larger level gives a strictly weaker guard, p. 1221. -/
theorem larger_level_guard_strict_loss (ε v z Z : ℝ)
    (he : -1 < ε) (hv : 1 < v) (hvz : v < z) (hzZ : z < Z) :
    (1 + ε) * (log z / log v) < (1 + ε) * (log Z / log v) := by
  exact mul_lt_mul_of_pos_left
    (div_lt_div_of_pos_right (log_lt_log (by linarith) hzZ) (log_pos hv)) (by linarith)

/-- A coarse reciprocal-log budget exceeds the required density error, p. 1227.
This is a scalar obstruction, not a counterexample to the density estimate. -/
theorem coarse_density_budget_strict_loss (L : ℝ) (hL : 3200 ≤ L) :
    0.62 * L / exp (L / 16) < 4 / L := by
  have hL0 : 0 < L := by linarith
  have he := pow_div_factorial_le_exp (x := L / 16) (by positivity) 4
  norm_num [Nat.factorial] at he
  have hL2 : 3200 ^ 2 ≤ L ^ 2 := by nlinarith
  have hm := mul_nonneg (show 0 ≤ L ^ 2 - 3200 ^ 2 by linarith) (sq_nonneg L)
  rw [div_lt_div_iff₀ (exp_pos _) hL0]
  nlinarith

/-- LEAF. First lower sieve inequality of Theorem 5, p. 1229 after display 19.
Construct the finite sequence and apply Theorem 4 and Lemma 7.
The strict inequality needs a strict density or cardinality step because the lab
LinearSieveT4 records non-strict inequalities. The small z source range also needs review. -/
theorem sieve_lower (α A u ε C₁ C₂ X₂ : ℝ) (n : ℕ)
    (hG : GRH) (hT : LinearSieveT4 ε C₁ C₂) (hL : Lemma7J)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (heps : epsJ u ≤ ε)
    (he0 : 0 < ε) (he1 : ε < 1 / 63) (hα : 0 < α) (hα1 : α < 1 / 8)
    (hA : 0 < A) (hc : Cond19 α A u X₂) (hX : 4e18 ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) :
    sieveMain n α ε C₂ - remainder n α u < (U7153.SA n : ℝ) := by
  have hX0 : 0 < X₂ := by linarith
  have hnlog : 3200 < log (n : ℝ) :=
    (EndpointC169.log_endpoint_gt α A u X₂ hα hα1 hA hc hX).trans_le
      (log_le_log hX0 hn)
  apply sieve_lower_of_band α u ε C₁ C₂ n hT hC₂ heps he0 he1 hα hα1 hc.2.2.1 hnlog hev
  intro z v hz huv hvz
  by_cases hlarge : exp 2753 < z
  · exact (hL z u v hlarge hc.2.2.1 huv hvz).1
  · exact PublishedInputs233.small_level_product z u v hz (le_of_not_gt hlarge)
      hc.2.2.1 huv hvz

/-- The common lower sieve cutoff lies below H, journal p. 1229.
CONDITIONAL ON Lemma 2. -/
theorem lower_cutoffs (h2 : PaperInputs148.Lemma2J)
    (α A u X : ℝ) (n : ℕ) (hα : 0 < α) (hα1 : α < 1 / 8)
    (hA : 0 < A) (hc : Cond19 α A u X) (hX : 4e18 ≤ X) (hn : X ≤ (n : ℝ)) :
    1e8 ≤ √(n : ℝ) / log n ^ (A + 1) ∧
      (smallProduct n u : ℝ) * (n : ℝ) ^ (1 / 2 - α) ≤
        √(n : ℝ) / log n ^ (A + 1) := by
  have hX1 : 1 < X := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 0 < log (n : ℝ) := log_pos (by linarith)
  have hP : 0 < log (n : ℝ) ^ (A + 1) := rpow_pos_of_pos hL _
  have h19 := DecompC169b.cond19_at α A u X n hα hA hc hX1 hn
  have htheta := h2 u (by linarith [hc.2.2.1]) hc.2.2.2
  have hQ : (smallProduct n u : ℝ) ≤ exp u :=
    (DecompC169b.smallProduct_le_exp_theta n u).trans (exp_le_exp.mpr htheta)
  have hprod : (n : ℝ) ^ α * (n : ℝ) ^ (1 / 2 - α) = √(n : ℝ) := by
    rw [← rpow_add hn0]
    convert (sqrt_eq_rpow (n : ℝ)).symm using 1 <;> congr 1 <;> ring
  constructor
  · have h := Journal.remark1_H hn1 (by linarith : α ≤ 1 / 2) hP hc.2.2.1 h19
    norm_num at h ⊢
    exact h
  · calc
      _ ≤ ((n : ℝ) ^ α / log n ^ (A + 1)) * (n : ℝ) ^ (1 / 2 - α) :=
        mul_le_mul_of_nonneg_right (hQ.trans h19) (rpow_nonneg hn0.le _)
      _ = _ := by rw [div_mul_eq_mul_div, hprod]

/-- Each lower sieve divisor is squarefree and coprime to n, p. 1229. -/
theorem lower_divisor_spec {n d : ℕ} {α u : ℝ} (hd : d ∈ sieveDivisors n α u) :
    Squarefree d ∧ Nat.Coprime d n ∧ 0 < d ∧
      (d : ℝ) < smallProduct n u * (n : ℝ) ^ (1 / 2 - α) := by
  obtain ⟨hdI, hdlt⟩ := mem_filter.mp hd
  obtain ⟨T, hT, rfl⟩ := mem_image.mp hdI
  have hp (p : ℕ) (hpT : p ∈ T) : p.Prime ∧ ¬ p ∣ n := by
    have h := mem_powerset.mp hT hpT
    exact ⟨(mem_filter.mp h).2.1, (mem_filter.mp h).2.2.1⟩
  have hsq : Squarefree (∏ p ∈ T, p) := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hpT r hrT hpr
      exact Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (hp p hpT).1 (hp r hrT).1).mpr hpr)
    · intro p hpT
      exact (hp p hpT).1.squarefree
  have hcop : Nat.Coprime (∏ p ∈ T, p) n := by
    apply Nat.coprime_prod_left_iff.mpr
    intro p hpT
    exact ((hp p hpT).1.coprime_iff_not_dvd).mpr (hp p hpT).2
  exact ⟨hsq, hcop, Nat.pos_of_ne_zero hsq.ne_zero, hdlt⟩

/-- The lower remainder follows from the explicit published inputs, pp. 1229 to 1231.
CONDITIONAL ON Lemmas 1, 2, 3, 4, 5 and GRH. -/
theorem remainder_bound_of_inputs (h1 : PaperInputs148.Lemma1J)
    (h2 : PaperInputs148.Lemma2J) (h4 : PaperInputs148.Lemma4J)
    (hMu : PaperInputs148.Lemma5MuJ) (α A u X₂ : ℝ) (n : ℕ)
    (hG : GRH) (h3 : Lemma3J) (hα : 0 < α) (hα1 : α < 1 / 8)
    (hA : 0 < A) (hc : Cond19 α A u X₂) (hX : 4e18 ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) :
    remainder n α u ≤ cGJ X₂ * n / log n ^ A := by
  obtain ⟨hH, hQD⟩ := lower_cutoffs h2 α A u X₂ n hα hα1 hA hc hX hn
  apply DecompC169b.squarefree_residue_sum h1 h4 hMu h3 hG n X₂ A
    (sieveDivisors n α u) hX hn hA hev hH
  intro d hd
  obtain ⟨hsq, hcop, hd0, hdlt⟩ := lower_divisor_spec hd
  exact ⟨hsq, hd0, hdlt.le.trans hQD, hcop⟩

/-- LEAF. Bound the lower sieve remainder by Lemmas 12 and 13, p. 1231 display 20.
Use Lemma 3, the squarefree modulus count in Lemma 5 and QD at most H on p. 1229. -/
theorem remainder_bound (α A u X₂ : ℝ) (n : ℕ)
    (hG : GRH) (h3 : Lemma3J) (hα : 0 < α) (hα1 : α < 1 / 8)
    (hA : 0 < A) (hc : Cond19 α A u X₂) (hX : 4e18 ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) :
    remainder n α u ≤ cGJ X₂ * n / log n ^ A := by
  exact remainder_bound_of_inputs PublishedInputs232.lemma1_schoenfeld
    PublishedInputs232.lemma2_theta PublishedInputs232.lemma4_robin
    PublishedInputs232.lemma5_mu α A u X₂ n hG h3 hα hα1 hA hc hX hn hev

/-- The fourth logarithmic power is below square root on the full condition 19 range.
This is the elementary error budget used on journal p. 1228. -/
theorem sqrt_log_four (N : ℝ) (hN : 0 < N) (hL : 3200 ≤ log N) :
    log N ^ 4 ≤ √N := by
  have he := pow_div_factorial_le_exp (x := log N / 2) (by linarith) 6
  have hs : exp (log N / 2) = √N := by
    rw [sqrt_eq_rpow, rpow_def_of_pos hN]
    congr 1
    ring
  rw [hs] at he
  norm_num [Nat.factorial] at he
  have hL2 : 46080 ≤ log N ^ 2 := by nlinarith
  have hm := mul_nonneg (show 0 ≤ log N ^ 2 - 46080 by linarith)
    (pow_nonneg (by linarith : 0 ≤ log N) 4)
  nlinarith

/-- The two errors fit into two N over log cubed N, journal p. 1228.
The condition 19 range suffices for this elementary estimate. -/
theorem lower_card_error_budget (N : ℝ) (hN : 0 < N) (hL : 3200 ≤ log N) :
    √N * log N / (8 * π) + 1.3841 * log N / log (log N) ≤ 2 * N / log N ^ 3 := by
  have hS := sqrt_log_four N hN hL
  have hlog : 1 ≤ log (log N) := by
    rw [le_log_iff_exp_le (by linarith)]
    linarith [exp_one_lt_d9]
  have hL0 : 0 < log N := by linarith
  have hS0 : 0 < √N := sqrt_pos.mpr hN
  have h4 : (2 : ℝ) ≤ log N ^ 4 := by nlinarith [sq_nonneg (log N ^ 2 - 2)]
  have hN2 : 2 * log N ^ 4 ≤ N := by
    have hm := mul_le_mul_of_nonneg_left hS hS0.le
    nlinarith [sq_sqrt hN.le]
  have hp : 1 ≤ 8 * π := by linarith [pi_gt_three]
  have h1 : √N * log N / (8 * π) ≤ N / log N ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hm := mul_le_mul_of_nonneg_left hS hS0.le
    have hm2 := mul_le_mul_of_nonneg_left hp hN.le
    nlinarith [sq_sqrt hN.le]
  have h2 : 1.3841 * log N / log (log N) ≤ N / log N ^ 3 := by
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    have hm := mul_le_mul_of_nonneg_left hlog hN.le
    nlinarith
  exact (add_le_add h1 h2).trans_eq (by ring)

/-- The lower cardinality bound holds on the full condition 19 range, p. 1228.
CONDITIONAL ON the prime count and Robin inputs and GRH. -/
theorem lower_cardinality (h1 : PaperInputs148.Lemma1J) (h4 : PaperInputs148.Lemma4J)
    (n : ℕ) (hG : GRH) (hn : (4e18 : ℝ) ≤ n) (hL : 3200 ≤ log (n : ℝ)) :
    (n : ℝ) / log n ≤ (U7153.Aset n).card := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hnNat : 0 < n := by exact_mod_cast hn0
  have hn3 : 3 ≤ n := by exact_mod_cast (show (3 : ℝ) ≤ n by linarith)
  have hL0 : 0 < log (n : ℝ) := by linarith
  have hpi := PaperInputs148.lemma1_of_grh h1 hG n (by linarith)
  simp only [PaperInputs148.primeCount, Nat.floor_natCast] at hpi
  have hω := (h4 n hn3).le
  have hli := (PublishedInputs232.li_bounds_large n
    ((le_log_iff_exp_le hn0).mp (by linarith : (11 : ℝ) ≤ log (n : ℝ)))).1
  have hcard : ((U7153.Aset n).card : ℝ) + n.primeFactors.card =
      (((range (n + 1)).filter Nat.Prime).card : ℝ) := by
    exact_mod_cast BookkeepingC164.count_identity n hnNat
  have herror := lower_card_error_budget n hn0 hL
  have hAlo : liPV n - 2 * (n : ℝ) / log n ^ 3 ≤ (U7153.Aset n).card := by
    linarith [(abs_le.mp hpi).1]
  have hnorm : (1 + 1 / log (n : ℝ)) * n / log n -
      2 * (n : ℝ) / log n ^ 3 =
        (n : ℝ) / log n + (n : ℝ) / log n ^ 3 * (log n - 2) := by
    field_simp
    <;> ring
  have hpos : 0 ≤ (n : ℝ) / log n ^ 3 * (log n - 2) := by
    exact mul_nonneg (by positivity) (by linarith)
  linarith

/-- The near-one density factor increases with the endpoint, journal p. 1229. -/
theorem lower_density_factor_mono (X Y : ℝ) (hX : 0 < X) (hL : 16 ≤ log X) (hXY : X ≤ Y) :
    1 - 0.62 * log X / X ^ (1 / 16 : ℝ) ≤
      1 - 0.62 * log Y / Y ^ (1 / 16 : ℝ) := by
  have hx : exp ((1 / 16 : ℝ)⁻¹) ≤ X := by
    norm_num
    exact (le_log_iff_exp_le hX).mp hL
  have h := log_div_self_rpow_antitoneOn (by norm_num : (0 : ℝ) < 1 / 16)
    hx (hx.trans hXY) hXY
  simp only [mul_div_assoc] at h ⊢
  linarith

/-- The endpoint comparison from the two explicit main-mass estimates, p. 1229.
CONDITIONAL ON the finite density and cardinality lower estimates. -/
theorem endpoint_comparison_of_estimates (α A ε C₂ X₂ : ℝ) (n : ℕ)
    (hX : 4e18 ≤ X₂) (hn : X₂ ≤ (n : ℝ)) (hLX : 3200 ≤ log X₂)
    (hcoef : 0 ≤ lowerCoefficient α ε C₂)
    (hdensity : 8 * UNfull n / log n *
      (1 - 0.62 * log n / (n : ℝ) ^ (1 / 16 : ℝ)) ≤ density n)
    (hcard : (n : ℝ) / log n ≤ (U7153.Aset n).card) :
    8 * (UNfull n * n / log n ^ 2) * B5J α A ε C₂ X₂ n ≤
      sieveMain n α ε C₂ - cGJ X₂ * n / log n ^ A := by
  have hX0 : 0 < X₂ := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hLX0 : 0 < log X₂ := by linarith
  have hLN : 0 < log (n : ℝ) := hLX0.trans_le (log_le_log hX0 hn)
  have hLNne : log (n : ℝ) ≠ 0 := hLN.ne'
  have hU : 0 < UNfull n := by linarith [two_fifths_le_UNfull n]
  let δ := 1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ)
  let scale := 8 * (UNfull n * n / log n ^ 2)
  have hδ : 0 < δ := EndpointC169.density_factor_pos X₂ hX0 hLX
  have hδle : δ ≤ 1 := by
    have hnn : 0 ≤ 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ) := by positivity
    dsimp [δ]
    linarith
  have hmono := lower_density_factor_mono X₂ n hX0 (by linarith) hn
  have hden : 8 * UNfull n / log n * δ ≤ density n :=
    (mul_le_mul_of_nonneg_left hmono (by positivity)).trans hdensity
  have hd0 : 0 ≤ density n := (show 0 ≤ 8 * UNfull n / log n * δ by positivity).trans hden
  have hmass := mul_le_mul hden hcard (div_nonneg hn0.le hLN.le) hd0
  have hnorm : (8 * UNfull n / log n * δ) * ((n : ℝ) / log n) = scale * δ := by
    dsimp [scale]
    field_simp
    <;> ring
  rw [hnorm] at hmass
  have hmain : scale * (δ * lowerCoefficient α ε C₂) ≤ sieveMain n α ε C₂ := by
    have h := mul_le_mul_of_nonneg_left hmass hcoef
    unfold sieveMain
    nlinarith
  have hTw : exp (-eulerMascheroniConstant) * LeanLab.ChenExplicit.twinC ≠ 0 :=
    (mul_pos (exp_pos _) LeanLab.ChenExplicit.twinC_pos).ne'
  have hUinv : UNfull n * invTw = 2 * UN n := by
    rw [UNfull_eq]
    unfold invTw
    field_simp [LeanLab.ChenExplicit.twinC_pos.ne']
    <;> ring
  have hUinv1 : 1 ≤ UNfull n * invTw := by
    rw [hUinv]
    linarith [one_le_UN n]
  have hδinv : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδle
  have hfactor : 1 ≤ UNfull n * invTw * δ⁻¹ := by nlinarith
  have hcG : 0 ≤ cGJ X₂ := EndpointC169.cGJ_nonneg X₂ hX0 (by linarith)
  have hPA : 0 < log (n : ℝ) ^ A := rpow_pos_of_pos hLN _
  have hPA2 : 0 < log (n : ℝ) ^ (A - 2) := rpow_pos_of_pos hLN _
  have hpow : log (n : ℝ) ^ A = log (n : ℝ) ^ (A - 2) * log n ^ 2 := by
    rw [← rpow_natCast, ← rpow_add hLN]
    congr 1
    norm_num
  have herrEq : scale * (1 / 8 * δ⁻¹ * invTw * cGJ X₂ / log (n : ℝ) ^ (A - 2)) =
      (UNfull n * invTw * δ⁻¹) * (cGJ X₂ * n / log (n : ℝ) ^ A) := by
    rw [hpow]
    dsimp [scale]
    field_simp
    <;> ring
  have herr : cGJ X₂ * n / log (n : ℝ) ^ A ≤
      scale * (1 / 8 * δ⁻¹ * invTw * cGJ X₂ / log (n : ℝ) ^ (A - 2)) := by
    rw [herrEq]
    exact le_mul_of_one_le_left (by positivity) hfactor
  change scale * (δ * lowerCoefficient α ε C₂ -
    1 / 8 * δ⁻¹ * invTw * cGJ X₂ / log (n : ℝ) ^ (A - 2)) ≤ _
  rw [mul_sub]
  linarith

/-- LEAF. Main term and endpoint comparisons in Theorem 5, pp. 1228 and 1229.
Use Lemmas 10 and 11 and monotonicity of the endpoint factors.
The conclusion retains the weaker error normalization of the exact lab B5J.
Treat a negative lower coefficient separately before multiplying density bounds. -/
theorem endpoint_comparison (α A u ε C₂ X₂ : ℝ) (n : ℕ)
    (hG : GRH) (hC₂ : 0 ≤ C₂) (he0 : 0 < ε) (he1 : ε < 1 / 63)
    (hα : 0 < α) (hα1 : α < 1 / 8) (hA : 0 < A) (hc : Cond19 α A u X₂)
    (hX : 4e18 ≤ X₂) (hn : X₂ ≤ (n : ℝ)) (hev : Even n)
    (hcoef : 0 ≤ lowerCoefficient α ε C₂) :
    8 * (UNfull n * n / log n ^ 2) * B5J α A ε C₂ X₂ n ≤
      sieveMain n α ε C₂ - cGJ X₂ * n / log n ^ A := by
  have hLX := (EndpointC169.log_endpoint_gt α A u X₂ hα hα1 hA hc hX).le
  exact endpoint_comparison_of_estimates α A ε C₂ X₂ n hX hn hLX hcoef
    (PublishedInputs233.density_lower n hG (hX.trans hn) hev)
    (lower_cardinality PublishedInputs232.lemma1_schoenfeld PublishedInputs232.lemma4_robin
      n hG (hX.trans hn) (hLX.trans (log_le_log (by linarith : 0 < X₂) hn)))

/-- LEAF. Positivity guards for the endpoint comparison, pp. 1228 and 1229 display 19.
Use the exponential part of condition 19 to bound log X2 below 3200.
The qG sign follows from its explicit formula or the nonnegative absolute error in Lemma 3. -/
theorem endpoint_factors (α A u X₂ : ℝ) (hG : GRH) (h3 : Lemma3J)
    (hα : 0 < α) (hα1 : α < 1 / 8) (hA : 0 < A)
    (hc : Cond19 α A u X₂) (hX : 4e18 ≤ X₂) :
    0 < 1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ) ∧ 0 ≤ cGJ X₂ := by
  have hL := EndpointC169.log_endpoint_gt α A u X₂ hα hα1 hA hc hX
  have hX0 : 0 < X₂ := by linarith
  exact ⟨EndpointC169.density_factor_pos X₂ hX0 hL.le,
    EndpointC169.cGJ_nonneg X₂ hX0 (by linarith)⟩

/-- The negative coefficient case is scalar algebra, Theorem 5 p. 1228.
The density factor and cG sign guards are explicit to avoid a false low-endpoint claim. -/
theorem negative_coefficient (α A ε C₂ X₂ : ℝ) (n : ℕ)
    (hX : 4e18 ≤ X₂) (hn : X₂ ≤ (n : ℝ))
    (hdelta : 0 < 1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ))
    (hcg : 0 ≤ cGJ X₂) (hcoef : lowerCoefficient α ε C₂ < 0) :
    8 * (UNfull n * n / log n ^ 2) * B5J α A ε C₂ X₂ n < (U7153.SA n : ℝ) := by
  have hn1 : (1 : ℝ) < n := by linarith
  have hlog : 0 < log (n : ℝ) := log_pos hn1
  have hU : 0 < UNfull n := by linarith [two_fifths_le_UNfull n]
  have hscale : 0 < 8 * (UNfull n * n / log n ^ 2) := by positivity
  have hInv : 0 ≤ invTw := by
    unfold invTw
    exact inv_nonneg.mpr (mul_nonneg (exp_pos _).le LeanLab.ChenExplicit.twinC_pos.le)
  have herr : 0 ≤ 1 / 8 * (1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ))⁻¹ *
      invTw * cGJ X₂ / log (n : ℝ) ^ (A - 2) := by positivity
  have hmain := mul_neg_of_pos_of_neg hdelta hcoef
  have hbracket : B5J α A ε C₂ X₂ n < 0 := by
    unfold B5J
    change (1 - 0.62 * log X₂ / X₂ ^ (1 / 16 : ℝ)) * lowerCoefficient α ε C₂ - _ < 0
    linarith
  exact (mul_neg_of_pos_of_neg hscale hbracket).trans_le (Nat.cast_nonneg _)

/-- The exact existing Thm5J, OPEN through the four leaves and reused C164 inputs. -/
theorem thm5J_of_inputs (h3 : Lemma3J) (h7 : Lemma7J) : Thm5J := by
  intro α A u ε C₁ C₂ X₂ n hG hT hC₁ hC₂ heps he0 he1 hα hα1 hA hc hX hn hev
  by_cases hcoef : 0 ≤ lowerCoefficient α ε C₂
  · have hs := sieve_lower α A u ε C₁ C₂ X₂ n hG hT h7
      hC₁ hC₂ heps he0 he1 hα hα1 hA hc hX hn hev
    have hr := remainder_bound α A u X₂ n hG h3
      hα hα1 hA hc hX hn hev
    have hm := endpoint_comparison α A u ε C₂ X₂ n hG hC₂ he0 he1 hα hα1 hA hc hX hn hev hcoef
    exact lt_of_le_of_lt (hm.trans (sub_le_sub_left hr _)) hs
  · obtain ⟨hd, hcg⟩ := endpoint_factors α A u X₂ hG h3 hα hα1 hA hc hX
    exact negative_coefficient α A ε C₂ X₂ n hX hn hd hcg (lt_of_not_ge hcoef)

/-- Exact Thm5J using the decomposed reciprocal estimates and task164 progression input. -/
theorem thm5J : Thm5J :=
  thm5J_of_inputs DecompC164a.lemma3J DecompC169c.lemma7J

end
end LeanLab.BS2022GRH.DecompC169a

#print axioms LeanLab.BS2022GRH.DecompC169a.sieve_lower
#print axioms LeanLab.BS2022GRH.DecompC169a.remainder_bound
#print axioms LeanLab.BS2022GRH.DecompC169a.endpoint_comparison
#print axioms LeanLab.BS2022GRH.DecompC169a.thm5J

#print axioms LeanLab.BS2022GRH.DecompC169a.negative_coefficient

#print axioms LeanLab.BS2022GRH.DecompC169a.endpoint_factors

#print axioms LeanLab.BS2022GRH.DecompC169a.thm5J_of_inputs
