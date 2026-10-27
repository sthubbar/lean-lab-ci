import LeanLab.PNTPort.BVMax.RenyiRem
import LeanLab.PNTSieve.SelbergBounds

/-
# U-1431, I-0104, track T2: discharging the Bombieri-Vinogradov input of the R-0034 and R-0037
# salvages with the lab's unconditional `bvPi` and `bvTheta`

Unit U-1431, PC run 20261021T1403Z-5629. AI-written Lean code, Claude. Checked only by the Lean
kernel. KNOWN mathematics: Bombieri-Vinogradov, Selberg's upper bound sieve. Binary Goldbach is
OPEN; an upper bound on r(N) is not progress on it.

Audit of the two route files. Neither `Routes/R0034.lean` nor `Routes/R0037.lean` states a
Bombieri-Vinogradov hypothesis: R0034 proves the majorant subtraction algebra and R0037 proves
Vaughan's identity, both unconditional. The phrases "CONDITIONAL ON Bombieri-Vinogradov" exist only
in prose, PROGRESS.md line 92 and R0037.md part (e). So there is nothing to relabel; this file
states the input the prose salvages need and discharges it.

Plain-math twins, statement by statement:
* `GoldbachBV`, the level 1/2 input for the sifted sequence {N - p : p < N prime}: for every A > 0
  there are B > 0 and K with, for every N ≥ 2,
  Σ_{d ≤ √N/(log N)^B, (d, N) = 1} |#{p < N : d ∣ N - p} - li(N - 1)/φ(d)| ≤ K N/(log N)^A.
  `goldbachBV_of_bvPi`, `goldbachBV`: PROVED from `bvPi`, unconditional.
* `card_dvd_goldbachSeq_le_one`: if (d, N) > 1 then #{p < N prime : d ∣ N - p} ≤ 1, since such p
  equals gcd(d, N). PROVED. So moduli sharing a factor with N cost at most 1 each.
* `GoldbachThetaBV`, the R-0037 Type I input with log weights:
  Σ_{d ≤ √N/(log N)^B, (d, N) = 1} |θ(N - 1; d, N) - (N - 1)/φ(d)| ≤ K N/(log N)^A, where
  θ(N - 1; d, N) = Σ_{p < N, p ≡ N mod d} log p = Σ_{p < N, d ∣ N - p} log p.
  `goldbachThetaBV`: PROVED from `bvTheta`.
* `rG_le_selberg`: for every N, z, level y ≥ 1, with P = ∏_{3 ≤ p ≤ z, p ∤ N} p,
  r(N) ≤ li(N - 1)/S + Σ_{d ∣ P, d ≤ y} 3^ω(d) |R_d| + z + 1, the Selberg Λ² upper bound on
  {N - p}, S the Selberg bounding sum Σ_{l ∣ P, l² ≤ y} g(l), g(p) = 1/(p - 2). PROVED.
* `rG_le_selberg_bv`, the R-0034 salvage with the BV input DISCHARGED: for every A > 0 there are
  B > 0 and K with, for all N ≥ 2, z and 1 ≤ y ≤ √N/(log N)^B,
  r(N) ≤ li(N - 1)/S + √((N + li(N - 1)) · M₉(N, z) · K N/(log N)^A) + z + 1,
  M₉(N, z) = Σ_{d ∣ P} 9^ω(d)/φ(d) = ∏_{p ∣ P} (1 + 9/(p - 1)). PROVED, unconditional.

What is NOT here: the lower bound S ≥ (1 - ε) (log y)/2 · ∏ local factors that turns li(N - 1)/S
into (4 + ε) times the Hardy-Littlewood main term, and the Mertens bound M₉ ≪ (log z)⁹. Both are
elementary multiplicative number theory; neither is a Bombieri-Vinogradov input.
-/

namespace LeanLab.Routes.U1431

open Finset LeanLab.PNTPort.BVMax
open scoped ArithmeticFunction.omega

/-! ## A. The level 1/2 input for {N - p}, from `bvPi` -/

/-- The input the R-0034 Selberg salvage needs: the Goldbach sequence has level 1/2 over all
moduli coprime to `N`. -/
def GoldbachBV : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ∑ d ∈ (Icc 1 ⌊Real.sqrt N / Real.log N ^ B⌋₊).filter (fun d => Nat.Coprime N d),
      |((((goldbachSeq N).filter (fun m => d ∣ m)).card : ℕ) : ℝ) -
        liD ((N - 1 : ℕ) : ℝ) / (d.totient : ℝ)| ≤ K * N / Real.log N ^ A

theorem goldbachBV_of_bvPi (h : BVPi) : GoldbachBV := by
  intro A hA
  obtain ⟨B, hB, K, hK⟩ := h A hA
  refine ⟨B, hB, K, fun N hN => ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set y : ℝ := ((N - 1 : ℕ) : ℝ) with hy
  set a : ℕ → ℕ := fun d => if Nat.Coprime N d then N else 1 with ha
  have hacop : ∀ d, Nat.Coprime (a d) d := by
    intro d; simp only [ha]; split_ifs with h
    · exact h
    · exact Nat.coprime_one_left d
  have hbv := hK N hN2 a hacop (fun _ => y)
    (fun _ => ⟨Nat.cast_nonneg _, by rw [hy]; exact_mod_cast Nat.sub_le N 1⟩)
  refine le_trans ?_ hbv
  rw [sum_filter]
  apply sum_le_sum
  intro d _
  split_ifs with hc
  · rw [card_dvd_goldbachSeq]
    have : piAP y d (a d) = piN (N - 1) d N := by
      simp only [ha, if_pos hc]; unfold piAP; rw [hy, Nat.floor_natCast]
    rw [this]
  · exact abs_nonneg _

/-- PROVED, unconditional. -/
theorem goldbachBV : GoldbachBV := goldbachBV_of_bvPi bvPi

/-- Moduli not coprime to `N` see at most one element of `{N - p}`. -/
theorem card_dvd_goldbachSeq_le_one {N d : ℕ} (h : ¬ Nat.Coprime N d) :
    ((goldbachSeq N).filter (fun m => d ∣ m)).card ≤ 1 := by
  have key : ∀ p, p < N → p.Prime → d ∣ N - p → p = Nat.gcd N d := by
    intro p hpN hp hdp
    have hgN : Nat.gcd N d ∣ N := Nat.gcd_dvd_left N d
    have hgd : Nat.gcd N d ∣ N - p := (Nat.gcd_dvd_right N d).trans hdp
    have hgN' : Nat.gcd N d ∣ (N - p) + p := by rwa [Nat.sub_add_cancel hpN.le]
    have hgp : Nat.gcd N d ∣ p := (Nat.dvd_add_right hgd).1 hgN'
    rcases (Nat.dvd_prime hp).1 hgp with h1 | h1
    · exact absurd h1 h
    · exact h1.symm
  rw [Finset.card_le_one]
  intro m1 h1 m2 h2
  simp only [goldbachSeq, mem_filter, mem_image, mem_range] at h1 h2
  obtain ⟨⟨p1, ⟨hp1N, hp1⟩, rfl⟩, hd1⟩ := h1
  obtain ⟨⟨p2, ⟨hp2N, hp2⟩, rfl⟩, hd2⟩ := h2
  rw [key p1 hp1N hp1 hd1, key p2 hp2N hp2 hd2]

/-- All moduli up to the level, coprime or not: the BV error plus at most one per modulus. -/
theorem goldbachBV_all : ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ∑ d ∈ Icc 1 ⌊Real.sqrt N / Real.log N ^ B⌋₊,
      |((((goldbachSeq N).filter (fun m => d ∣ m)).card : ℕ) : ℝ) -
        (if Nat.Coprime N d then liD ((N - 1 : ℕ) : ℝ) / (d.totient : ℝ) else 0)| ≤
      K * N / Real.log N ^ A + ⌊Real.sqrt N / Real.log N ^ B⌋₊ := by
  intro A hA
  obtain ⟨B, hB, K, hK⟩ := goldbachBV A hA
  refine ⟨B, hB, K, fun N hN => ?_⟩
  set Q := ⌊Real.sqrt N / Real.log N ^ B⌋₊
  rw [← sum_filter_add_sum_filter_not (Icc 1 Q) (fun d => Nat.Coprime N d)]
  gcongr
  · apply le_of_eq_of_le _ (hK N hN)
    refine sum_congr rfl (fun d hd => ?_)
    rw [if_pos (mem_filter.1 hd).2]
  · calc _ ≤ ∑ d ∈ (Icc 1 Q).filter (fun d => ¬ Nat.Coprime N d), (1 : ℝ) := by
          apply sum_le_sum
          intro d hd
          rw [if_neg (mem_filter.1 hd).2, sub_zero, abs_of_nonneg (Nat.cast_nonneg _)]
          exact_mod_cast card_dvd_goldbachSeq_le_one (mem_filter.1 hd).2
      _ ≤ ∑ d ∈ Icc 1 Q, (1 : ℝ) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => zero_le_one)
      _ = Q := by simp

/-! ## B. The R-0037 Type I input with log weights, from `bvTheta` -/

def GoldbachThetaBV : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ∑ d ∈ (Icc 1 ⌊Real.sqrt N / Real.log N ^ B⌋₊).filter (fun d => Nat.Coprime N d),
      |thetaN (N - 1) d N - ((N - 1 : ℕ) : ℝ) / (d.totient : ℝ)| ≤ K * N / Real.log N ^ A

theorem goldbachThetaBV_of_bvTheta (h : BVTheta) : GoldbachThetaBV := by
  intro A hA
  obtain ⟨B, hB, K, hK⟩ := h A hA
  refine ⟨B, hB, K, fun N hN => ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set y : ℝ := ((N - 1 : ℕ) : ℝ) with hy
  set a : ℕ → ℕ := fun d => if Nat.Coprime N d then N else 1 with ha
  have hacop : ∀ d, Nat.Coprime (a d) d := by
    intro d; simp only [ha]; split_ifs with h
    · exact h
    · exact Nat.coprime_one_left d
  have hbv := hK N hN2 a hacop (fun _ => y)
    (fun _ => ⟨Nat.cast_nonneg _, by rw [hy]; exact_mod_cast Nat.sub_le N 1⟩)
  refine le_trans ?_ hbv
  rw [sum_filter]
  apply sum_le_sum
  intro d _
  split_ifs with hc
  · have : thetaAP y d (a d) = thetaN (N - 1) d N := by
      simp only [ha, if_pos hc]; unfold thetaAP; rw [hy, Nat.floor_natCast]
    rw [this]
  · exact abs_nonneg _

/-- PROVED, unconditional. -/
theorem goldbachThetaBV : GoldbachThetaBV := goldbachThetaBV_of_bvTheta bvTheta

/-- Plain-math twin of the left side of `GoldbachThetaBV`: `θ(N - 1; d, N)` is the sum of `log p`
over primes `p < N` with `d ∣ N - p`. -/
theorem thetaN_eq_goldbach (N d : ℕ) :
    thetaN (N - 1) d N =
      ∑ p ∈ (range N).filter (fun p => p.Prime ∧ d ∣ N - p), Real.log p := by
  unfold thetaN
  apply sum_congr _ (fun _ _ => rfl)
  ext p
  simp only [mem_filter, mem_Icc, mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, hmod, hp⟩
    exact ⟨by omega, hp, (Nat.modEq_iff_dvd' (by omega)).mp hmod⟩
  · rintro ⟨hpN, hp, hd⟩
    exact ⟨⟨hp.one_lt.le, by omega⟩, (Nat.modEq_iff_dvd' hpN.le).mpr hd, hp⟩

/-! ## C. Selberg's upper bound sieve on {N - p} -/

/-- The binary Goldbach count `#{p < N : p, N - p prime}`, as in `SchnirelmannGoldbach.r`. -/
noncomputable def rG (N : ℕ) : ℕ := ((range N).filter (fun p => p.Prime ∧ (N - p).Prime)).card

/-- Sifting primes `3 ≤ p ≤ z`, `p ∤ N`. -/
def Pset (N z : ℕ) : Finset ℕ := (range (z + 1)).filter (fun p => p.Prime ∧ 3 ≤ p ∧ ¬ p ∣ N)

lemma mem_Pset {N z p : ℕ} : p ∈ Pset N z ↔ p ≤ z ∧ p.Prime ∧ 3 ≤ p ∧ ¬ p ∣ N := by
  simp [Pset, Nat.lt_succ_iff]

def Pprod (N z : ℕ) : ℕ := ∏ p ∈ Pset N z, p

lemma Pprod_coprime (N z : ℕ) : Nat.Coprime (Pprod N z) N :=
  coprime_prod_primes _ N (fun p hp => ⟨(mem_Pset.1 hp).2.1, (mem_Pset.1 hp).2.2.2⟩)

lemma Pprod_ne_zero (N z : ℕ) : Pprod N z ≠ 0 :=
  prod_ne_zero_iff.mpr (fun p hp => (mem_Pset.1 hp).2.1.ne_zero)

lemma prime_dvd_Pprod {N z p : ℕ} (hp : p.Prime) (h : p ∣ Pprod N z) : p ∈ Pset N z := by
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 h
  have hqp := (mem_Pset.1 hq).2.1
  rwa [(Nat.prime_dvd_prime_iff_eq hp hqp).1 hpq]

/-- `ν(d) = 1_{(d, N) = 1}/φ(d)`. -/
noncomputable def nuG (N : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => if Nat.Coprime d N then ((d.totient : ℝ))⁻¹ else 0, by simp⟩

lemma nuG_apply (N d : ℕ) :
    nuG N d = if Nat.Coprime d N then ((d.totient : ℝ))⁻¹ else 0 := rfl

lemma nuG_mult (N : ℕ) : (nuG N).IsMultiplicative := by
  refine ⟨by simp [nuG_apply], fun {m n} hmn => ?_⟩
  simp only [nuG_apply, Nat.coprime_mul_iff_left, Nat.totient_mul hmn, Nat.cast_mul, mul_inv]
  by_cases h1 : Nat.Coprime m N
  · by_cases h2 : Nat.Coprime n N
    · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2]
    · rw [if_neg (fun h => h2 h.2), if_neg h2, mul_zero]
  · rw [if_neg (fun h => h1 h.1), if_neg h1, zero_mul]

lemma nuG_prime_bounds {N z p : ℕ} (hp : p ∈ Pset N z) : 0 < nuG N p ∧ nuG N p < 1 := by
  obtain ⟨_, hpr, h3, hpN⟩ := mem_Pset.1 hp
  have hc : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hpr).2 hpN
  rw [nuG_apply, if_pos hc, Nat.totient_prime hpr]
  have h3' : (3 : ℝ) ≤ p := by exact_mod_cast h3
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hcast]
  exact ⟨inv_pos.2 (by linarith), inv_lt_one_of_one_lt₀ (by linarith)⟩

/-- The Selberg sieve on `{N - p : p < N prime}`, weights 1, mass `li(N - 1)`, density `ν`. -/
noncomputable def gbSieve (N z : ℕ) (y : ℝ) (hy : 1 ≤ y) : SelbergSieve where
  support := goldbachSeq N
  prodPrimes := Pprod N z
  prodPrimes_squarefree :=
    LeanLab.PNTSieve.Sieve.prodDistinctPrimes_squarefree _ (fun p hp => (mem_Pset.1 hp).2.1)
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := liD ((N - 1 : ℕ) : ℝ)
  nu := nuG N
  nu_mult := nuG_mult N
  nu_pos_of_prime := fun _ hp hd => (nuG_prime_bounds (prime_dvd_Pprod hp hd)).1
  nu_lt_one_of_prime := fun _ hp hd => (nuG_prime_bounds (prime_dvd_Pprod hp hd)).2
  level := y
  one_le_level := hy

lemma siftedSum_gbSieve (N z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    BoundingSieve.siftedSum (s := (gbSieve N z y hy).toBoundingSieve) =
      (((goldbachSeq N).filter (fun m => Nat.Coprime (Pprod N z) m)).card : ℝ) := by
  unfold BoundingSieve.siftedSum
  exact sum_boole _ _

lemma rem_gbSieve (N z : ℕ) (y : ℝ) (hy : 1 ≤ y) {d : ℕ} (hd : d ∣ Pprod N z) :
    BoundingSieve.rem (s := (gbSieve N z y hy).toBoundingSieve) d =
      (((goldbachSeq N).filter (fun m => d ∣ m)).card : ℝ) -
        liD ((N - 1 : ℕ) : ℝ) / (d.totient : ℝ) := by
  have hc : Nat.Coprime d N := Nat.Coprime.coprime_dvd_left hd (Pprod_coprime N z)
  unfold BoundingSieve.rem BoundingSieve.multSum
  have h1 : ∑ n ∈ (gbSieve N z y hy).support, (if d ∣ n then (gbSieve N z y hy).weights n else 0)
      = (((goldbachSeq N).filter (fun m => d ∣ m)).card : ℝ) := sum_boole _ _
  rw [h1]
  show _ - nuG N d * liD ((N - 1 : ℕ) : ℝ) = _
  rw [nuG_apply, if_pos hc, inv_mul_eq_div]

/-- Goldbach pairs with `N - p > z` survive the sieve; the rest number at most `z + 1`. -/
theorem rG_le_sifted (N z : ℕ) :
    rG N ≤ ((goldbachSeq N).filter (fun m => Nat.Coprime (Pprod N z) m)).card + (z + 1) := by
  unfold rG
  set G := (range N).filter (fun p => p.Prime ∧ (N - p).Prime)
  rw [← card_filter_add_card_filter_not (s := G) (fun p => z < N - p)]
  apply add_le_add
  · apply card_le_card_of_injOn (fun p => N - p)
    · intro p hp
      simp only [G, coe_filter, mem_filter, mem_range, Set.mem_setOf_eq] at hp
      obtain ⟨⟨hpN, hp, hq⟩, hz⟩ := hp
      simp only [coe_filter, Set.mem_setOf_eq, mem_filter]
      refine ⟨?_, ?_⟩
      · simp only [goldbachSeq, mem_image, mem_filter, mem_range]
        exact ⟨p, ⟨hpN, hp⟩, rfl⟩
      · apply Nat.Coprime.prod_left
        intro q hq'
        obtain ⟨hqz, hqp, _, _⟩ := mem_Pset.1 hq'
        exact (Nat.coprime_primes hqp hq).2 (by omega)
    · intro a ha b hb he
      simp only [G, coe_filter, mem_filter, mem_range, Set.mem_setOf_eq] at ha hb
      simp only at he
      omega
  · calc _ ≤ (range (z + 1)).card := by
          apply card_le_card_of_injOn (fun p => N - p)
          · intro p hp
            simp only [coe_filter, mem_filter, Set.mem_setOf_eq, G, mem_range] at hp
            simp only [coe_range, Set.mem_Iio]
            omega
          · intro a ha b hb he
            simp only [G, coe_filter, mem_filter, mem_range, Set.mem_setOf_eq] at ha hb
            simp only at he
            omega
      _ = z + 1 := card_range _

open LeanLab.PNTSieve.SelbergSieve in
/-- Selberg's upper bound on `{N - p}`, unconditional: `r(N) ≤ li(N - 1)/S + Σ_{d ∣ P, d ≤ y}
3^ω(d) |R_d| + z + 1`. -/
theorem rG_le_selberg (N z : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    (rG N : ℝ) ≤ liD ((N - 1 : ℕ) : ℝ) / selbergBoundingSum (gbSieve N z y hy) +
      ∑ d ∈ (Pprod N z).divisors, (if (d : ℝ) ≤ y then (3 : ℝ) ^ ω d *
        |(((goldbachSeq N).filter (fun m => d ∣ m)).card : ℝ) -
          liD ((N - 1 : ℕ) : ℝ) / (d.totient : ℝ)| else 0) + (z + 1) := by
  have h1 : (rG N : ℝ) ≤
      (((goldbachSeq N).filter (fun m => Nat.Coprime (Pprod N z) m)).card : ℝ) + (z + 1) := by
    exact_mod_cast rG_le_sifted N z
  have h2 := selberg_bound_simple (gbSieve N z y hy)
  rw [siftedSum_gbSieve] at h2
  have h3 : ∑ d ∈ (Pprod N z).divisors, (if (d : ℝ) ≤ y then (3 : ℝ) ^ ω d *
        |BoundingSieve.rem (s := (gbSieve N z y hy).toBoundingSieve) d| else 0) =
      ∑ d ∈ (Pprod N z).divisors, (if (d : ℝ) ≤ y then (3 : ℝ) ^ ω d *
        |(((goldbachSeq N).filter (fun m => d ∣ m)).card : ℝ) -
          liD ((N - 1 : ℕ) : ℝ) / (d.totient : ℝ)| else 0) := by
    refine sum_congr rfl (fun d hd => ?_)
    rw [rem_gbSieve N z y hy (Nat.dvd_of_mem_divisors hd)]
  have h2' : (((goldbachSeq N).filter (fun m => Nat.Coprime (Pprod N z) m)).card : ℝ) ≤
      liD ((N - 1 : ℕ) : ℝ) / selbergBoundingSum (gbSieve N z y hy) +
      ∑ d ∈ (Pprod N z).divisors, (if (d : ℝ) ≤ y then (3 : ℝ) ^ ω d *
        |BoundingSieve.rem (s := (gbSieve N z y hy).toBoundingSieve) d| else 0) := h2
  rw [h3] at h2'
  linarith

/-! ## D. The remainder sum, with `goldbachBV` -/

/-- Weighted Cauchy-Schwarz: `(Σ w E)² ≤ (Σ w² E)(Σ E)` for `E ≥ 0`. -/
lemma cs_weighted (T : Finset ℕ) (w E : ℕ → ℝ) (hE : ∀ d, 0 ≤ E d) :
    (∑ d ∈ T, w d * E d) ^ 2 ≤ (∑ d ∈ T, w d ^ 2 * E d) * ∑ d ∈ T, E d := by
  have h := sum_mul_sq_le_sq_mul_sq T (fun d => w d * Real.sqrt (E d)) (fun d => Real.sqrt (E d))
  have h1 : ∀ d, w d * Real.sqrt (E d) * Real.sqrt (E d) = w d * E d := by
    intro d; rw [mul_assoc, Real.mul_self_sqrt (hE d)]
  have h2 : ∀ d, (w d * Real.sqrt (E d)) ^ 2 = w d ^ 2 * E d := by
    intro d; rw [mul_pow, Real.sq_sqrt (hE d)]
  have h3 : ∀ d, Real.sqrt (E d) ^ 2 = E d := fun d => Real.sq_sqrt (hE d)
  simp only [h1, h2, h3] at h
  exact h

lemma liD_nonneg (y : ℝ) : 0 ≤ liD y := by
  unfold liD liN
  apply sum_nonneg
  intro n hn
  have : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.1 hn).1
  exact div_nonneg zero_le_one (Real.log_nonneg this)

/-- `#{p < N : d ∣ N - p} ≤ N/d`. -/
lemma card_dvd_goldbachSeq_le (N d : ℕ) :
    (((goldbachSeq N).filter (fun m => d ∣ m)).card : ℝ) ≤ (N : ℝ) / d := by
  have hsub : (goldbachSeq N).filter (fun m => d ∣ m) ⊆ (Ioc 0 N).filter (fun m => d ∣ m) := by
    intro m hm
    simp only [goldbachSeq, mem_filter, mem_image, mem_range, mem_Ioc] at hm ⊢
    obtain ⟨⟨p, ⟨hpN, _⟩, rfl⟩, hd⟩ := hm
    exact ⟨⟨by omega, by omega⟩, hd⟩
  calc (((goldbachSeq N).filter (fun m => d ∣ m)).card : ℝ)
      ≤ (((Ioc 0 N).filter (fun m => d ∣ m)).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ = ((N / d : ℕ) : ℝ) := by rw [Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ (N : ℝ) / d := Nat.cast_div_le

/-- `|R_d| ≤ (N + li(N - 1))/φ(d)` for `d ≥ 1`. -/
lemma abs_rem_le (N d : ℕ) (hd : d ≠ 0) :
    |(((goldbachSeq N).filter (fun m => d ∣ m)).card : ℝ) -
        liD ((N - 1 : ℕ) : ℝ) / (d.totient : ℝ)| ≤
      ((N : ℝ) + liD ((N - 1 : ℕ) : ℝ)) / (d.totient : ℝ) := by
  have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hd)
  have hφd : (d.totient : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
  have hX := liD_nonneg ((N - 1 : ℕ) : ℝ)
  have hc0 : (0 : ℝ) ≤ (((goldbachSeq N).filter (fun m => d ∣ m)).card : ℝ) := Nat.cast_nonneg _
  have hc : (((goldbachSeq N).filter (fun m => d ∣ m)).card : ℝ) ≤ (N : ℝ) / d.totient :=
    (card_dvd_goldbachSeq_le N d).trans
      (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hφ hφd)
  have hXφ : 0 ≤ liD ((N - 1 : ℕ) : ℝ) / (d.totient : ℝ) := div_nonneg hX hφ.le
  rw [add_div, abs_le]
  constructor <;> linarith

/-- `M₉(N, z) = Σ_{d ∣ P} 9^ω(d)/φ(d)`. -/
noncomputable def M9 (N z : ℕ) : ℝ := ∑ d ∈ (Pprod N z).divisors, (9 : ℝ) ^ ω d / (d.totient : ℝ)

open LeanLab.PNTSieve.SelbergSieve in
/-- The R-0034 Selberg salvage with the Bombieri-Vinogradov input discharged by `bvPi`. PROVED,
unconditional. -/
theorem rG_le_selberg_bv (A : ℝ) (hA : 0 < A) : ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, ∀ N : ℕ, 2 ≤ N →
    ∀ z : ℕ, ∀ y : ℝ, ∀ hy : 1 ≤ y, y ≤ Real.sqrt N / Real.log N ^ B →
    (rG N : ℝ) ≤ liD ((N - 1 : ℕ) : ℝ) / selbergBoundingSum (gbSieve N z y hy) +
      Real.sqrt (((N : ℝ) + liD ((N - 1 : ℕ) : ℝ)) * M9 N z * (K * N / Real.log N ^ A)) +
      (z + 1) := by
  obtain ⟨B, hB, K, hK⟩ := goldbachBV A hA
  refine ⟨B, hB, K, fun N hN z y hy hyQ => ?_⟩
  have hsel := rG_le_selberg N z y hy
  set X := liD ((N - 1 : ℕ) : ℝ) with hXdef
  set E : ℕ → ℝ := fun d => |(((goldbachSeq N).filter (fun m => d ∣ m)).card : ℝ) -
      X / (d.totient : ℝ)| with hEdef
  set T := (Pprod N z).divisors.filter (fun d : ℕ => (d : ℝ) ≤ y) with hT
  have hErr : ∑ d ∈ (Pprod N z).divisors, (if (d : ℝ) ≤ y then (3 : ℝ) ^ ω d * E d else 0) =
      ∑ d ∈ T, (3 : ℝ) ^ ω d * E d := by rw [hT, sum_filter]
  have hE0 : ∀ d, 0 ≤ E d := fun d => abs_nonneg _
  -- the unweighted remainder sum, from goldbachBV
  have hsumE : ∑ d ∈ T, E d ≤ K * N / Real.log N ^ A := by
    refine le_trans ?_ (hK N hN)
    apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => abs_nonneg _)
    intro d hd
    rw [hT, mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdP, _⟩, hdy⟩ := hd
    have hd0 : d ≠ 0 := fun h => Pprod_ne_zero N z (by rw [h] at hdP; exact zero_dvd_iff.1 hdP)
    rw [mem_filter, mem_Icc]
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr hd0, Nat.le_floor (hdy.trans hyQ)⟩, ?_⟩
    exact (Nat.Coprime.coprime_dvd_left hdP (Pprod_coprime N z)).symm
  -- the 9^ω moment
  have hsum9 : ∑ d ∈ T, ((3 : ℝ) ^ ω d) ^ 2 * E d ≤ ((N : ℝ) + X) * M9 N z := by
    have hNX : 0 ≤ (N : ℝ) + X := add_nonneg (Nat.cast_nonneg _) (liD_nonneg _)
    calc ∑ d ∈ T, ((3 : ℝ) ^ ω d) ^ 2 * E d
        ≤ ∑ d ∈ T, (9 : ℝ) ^ ω d * (((N : ℝ) + X) / (d.totient : ℝ)) := by
          apply sum_le_sum
          intro d hd
          have hd0 : d ≠ 0 := Nat.pos_iff_ne_zero.mp
            (Nat.pos_of_mem_divisors (mem_filter.1 hd).1)
          have h9 : ((3 : ℝ) ^ ω d) ^ 2 = (9 : ℝ) ^ ω d := by
            rw [← pow_mul, mul_comm, pow_mul]; norm_num
          rw [h9]
          exact mul_le_mul_of_nonneg_left (abs_rem_le N d hd0) (by positivity)
      _ ≤ ∑ d ∈ (Pprod N z).divisors, (9 : ℝ) ^ ω d * (((N : ℝ) + X) / (d.totient : ℝ)) := by
          apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          intro d _ _
          exact mul_nonneg (by positivity) (div_nonneg hNX (Nat.cast_nonneg _))
      _ = ((N : ℝ) + X) * M9 N z := by
          rw [M9, mul_sum]
          refine sum_congr rfl (fun d _ => ?_)
          ring
  have hcs := cs_weighted T (fun d => (3 : ℝ) ^ ω d) E hE0
  have hsq : (∑ d ∈ T, (3 : ℝ) ^ ω d * E d) ^ 2 ≤
      ((N : ℝ) + X) * M9 N z * (K * N / Real.log N ^ A) := by
    refine hcs.trans ?_
    have hS0 : 0 ≤ ∑ d ∈ T, E d := sum_nonneg (fun d _ => hE0 d)
    have hR0 : 0 ≤ ((N : ℝ) + X) * M9 N z :=
      le_trans (sum_nonneg (fun d _ => mul_nonneg (by positivity) (hE0 d))) hsum9
    exact mul_le_mul hsum9 hsumE hS0 hR0
  have hroot : ∑ d ∈ T, (3 : ℝ) ^ ω d * E d ≤
      Real.sqrt (((N : ℝ) + X) * M9 N z * (K * N / Real.log N ^ A)) :=
    (le_abs_self _).trans (Real.abs_le_sqrt hsq)
  have hsel' : (rG N : ℝ) ≤ X / selbergBoundingSum (gbSieve N z y hy) +
      ∑ d ∈ (Pprod N z).divisors, (if (d : ℝ) ≤ y then (3 : ℝ) ^ ω d * E d else 0) + (z + 1) :=
    hsel
  rw [hErr] at hsel'
  linarith

/-! ## E. Vacuity instances -/

/-- `goldbachSeq 10 = {8, 7, 5, 3}`; the modulus `3`, coprime to `10`, sees exactly `3`. -/
theorem vacuity_coprime : ((goldbachSeq 10).filter (fun m => 3 ∣ m)).card = 1 := by decide

/-- The modulus `2`, not coprime to `10`, sees exactly `8 = 10 - 2`: the bound `≤ 1` is attained. -/
theorem vacuity_not_coprime : ((goldbachSeq 10).filter (fun m => 2 ∣ m)).card = 1 ∧
    ¬ Nat.Coprime 10 2 := by decide

/-- The sieve at `N = 10`, `z = 3`: `P = 3`, and `r(10) = 3`, so `rG_le_sifted` is a live
inequality `3 ≤ #{m ∈ {8,7,5,3} : (3, m) = 1} + 4 = 3 + 4`. -/
theorem vacuity_sieve : Pprod 10 3 = 3 ∧ rG 10 = 3 ∧
    ((goldbachSeq 10).filter (fun m => Nat.Coprime (Pprod 10 3) m)).card = 3 := by
  have hP : Pprod 10 3 = 3 := by decide
  refine ⟨hP, by decide, ?_⟩
  rw [hP]; decide

/-- The level window of `rG_le_selberg_bv` is nonempty: for `B = 1`, `N = 100`,
`1 ≤ √100/log 100`, so `y = 1` is admissible and the theorem is a live statement there. -/
theorem vacuity_level : (1 : ℝ) ≤ Real.sqrt ((100 : ℕ) : ℝ) / Real.log ((100 : ℕ) : ℝ) ^ (1 : ℝ) := by
  have h10 : Real.sqrt ((100 : ℕ) : ℝ) = 10 := by
    rw [show ((100 : ℕ) : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h10, Real.rpow_one]
  have he : Real.exp 10 = Real.exp (5 / 2) ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h35 : (7 / 2 : ℝ) ≤ Real.exp (5 / 2) := by
    have := Real.add_one_le_exp (5 / 2 : ℝ); linarith
  have hexp : (100 : ℝ) < Real.exp 10 := by
    rw [he]
    have : (7 / 2 : ℝ) ^ 4 ≤ Real.exp (5 / 2) ^ 4 := pow_le_pow_left₀ (by norm_num) h35 4
    nlinarith
  have hlog : Real.log ((100 : ℕ) : ℝ) < 10 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]; exact_mod_cast hexp
  have hlogpos : 0 < Real.log ((100 : ℕ) : ℝ) := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlogpos]; linarith

end LeanLab.Routes.U1431

#print axioms LeanLab.Routes.U1431.goldbachBV
#print axioms LeanLab.Routes.U1431.goldbachBV_all
#print axioms LeanLab.Routes.U1431.goldbachThetaBV
#print axioms LeanLab.Routes.U1431.thetaN_eq_goldbach
#print axioms LeanLab.Routes.U1431.card_dvd_goldbachSeq_le_one
#print axioms LeanLab.Routes.U1431.rG_le_sifted
#print axioms LeanLab.Routes.U1431.rG_le_selberg
#print axioms LeanLab.Routes.U1431.rG_le_selberg_bv
#print axioms LeanLab.Routes.U1431.vacuity_coprime
#print axioms LeanLab.Routes.U1431.vacuity_not_coprime
#print axioms LeanLab.Routes.U1431.vacuity_sieve
#print axioms LeanLab.Routes.U1431.vacuity_level
