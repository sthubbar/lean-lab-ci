import LeanLab.Ricci1937.TheoremsCD
import LeanLab.Ricci1937.CFactorBounds
import LeanLab.Brun1919.Sieve
import LeanLab.PNTSieve.MertensProduct
import LeanLab.PNTSieve.MertensLower
import LeanLab.PNTSieve.BrunPure
import LeanLab.Ricci1937.Tau23
import LeanLab.Ricci1937.Section2
import LeanLab.Ricci1937.SigmaBar
import LeanLab.PNTSieve.BrunBlocksRel
import LeanLab.SchnirelmannGoldbach.PureSieve

/-!
Ricci 1937, Theorem D, pages 88 and 89.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real Asymptotics
open LeanLab.PNTSieve.Mertens

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 89 survivor inclusion: roughness below N forces the factor count. -/
lemma decompJ365_almostGT_of_lt {x a N : ℕ} (hx : 1 ≤ x) (hN : x < N)
    (hr : ∀ p ∈ x.primeFactorsList, (N : ℝ) ^ (1 / ((a : ℝ) + 1)) < p) :
    AlmostGT a ((N : ℝ) ^ (1 / ((a : ℝ) + 1))) x := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  apply almostGT_of_pow_bound hx (Real.one_le_rpow hN1 (by positivity)) hr
  have hp : ((N : ℝ) ^ (1 / ((a : ℝ) + 1))) ^ (a + 1) = N := by
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num [Nat.cast_add, Nat.cast_one, ne_of_gt (show (0 : ℝ) < a + 1 by positivity)]
  rw [hp]
  exact_mod_cast hN

/-- Page 89: the W predicate is exactly the two prime roughness conditions. -/
lemma decompJ365_wCount_eq_rough (a b N : ℕ) :
    wCount a b N = #{A ∈ Icc 1 (N - 1) |
      (∀ p : ℕ, p ∈ A.primeFactorsList → (N : ℝ) ^ (1 / ((a : ℝ) + 1)) < (p : ℝ)) ∧
      ∀ p : ℕ, p ∈ (N - A).primeFactorsList → (N : ℝ) ^ (1 / ((b : ℝ) + 1)) < (p : ℝ)} := by
  unfold wCount
  congr 1
  apply filter_congr
  intro A hA
  rcases mem_Icc.mp hA with ⟨hA1, hAN⟩
  have hAN' : A < N := by omega
  constructor
  · intro h
    exact ⟨h.1.2.2, h.2.2.2⟩
  · intro h
    exact ⟨decompJ365_almostGT_of_lt hA1 hAN' h.1, decompJ365_almostGT_of_lt (by omega) (by omega) h.2⟩

/-- Page 89: every positive power saving is negligible relative to N over log squared N. -/
lemma decompJ365_power_isLittleO_div_log_sq {κ : ℝ} (hκ : 0 < κ) :
    (fun x : ℝ => x ^ (1 - κ)) =o[atTop] (fun x => x / Real.log x ^ 2) := by
  have hlog : (fun x : ℝ => Real.log x ^ 2) =o[atTop] (fun x => x ^ κ) := by
    simpa only [Real.rpow_two] using isLittleO_log_rpow_rpow_atTop (2 : ℝ) hκ
  have hprod := hlog.mul_isBigO (isBigO_refl (fun x : ℝ => x ^ (1 - κ)) atTop)
  have hprod' : (fun x : ℝ => Real.log x ^ 2 * x ^ (1 - κ)) =o[atTop] (fun x => x) := by
    apply hprod.congr' (Eventually.of_forall fun _ => rfl)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_add hx]
    norm_num
  apply (isLittleO_mul_iff_isLittleO_div (f := fun x : ℝ => Real.log x ^ 2)
    (g := fun x : ℝ => x ^ (1 - κ)) (h := fun x : ℝ => x) ?_).mp hprod'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact pow_ne_zero _ (Real.log_pos hx).ne'

/-- Page 89: a fixed saved power remainder is eventually below half the main term. -/
lemma decompJ365_power_error_absorb {κ a : ℝ} (hκ : 0 < κ) (ha : 0 < a) (A : ℝ) :
    ∀ᶠ n : ℕ in atTop, A * (n : ℝ) ^ (1 - κ) ≤ (a / 2) * n / Real.log n ^ 2 := by
  have hsmall := ((decompJ365_power_isLittleO_div_log_sq hκ).const_mul_left A).natCast_atTop
  filter_upwards [hsmall.def (by positivity : (0 : ℝ) < a / 2), eventually_ge_atTop 2]
    with n hn hn2
  have hnR : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hdivpos : 0 < (n : ℝ) / Real.log n ^ 2 := div_pos (by linarith) (sq_pos_of_pos (Real.log_pos hnR))
  calc
    A * (n : ℝ) ^ (1 - κ) ≤ |A * (n : ℝ) ^ (1 - κ)| := le_abs_self _
    _ ≤ (a / 2) * |(n : ℝ) / Real.log n ^ 2| := by simpa only [Real.norm_eq_abs] using hn
    _ = (a / 2) * n / Real.log n ^ 2 := by rw [abs_of_pos hdivpos]; ring

/-- Page 88: the local root count for H = X times X minus N is one or two. -/
lemma decompJ365_local_roots (p N : ℕ) [Fact p.Prime] :
    #{x : ZMod p | x * (x - (N : ZMod p)) = 0} =
      if (N : ZMod p) = 0 then 1 else 2 := by
  have hset : (Finset.univ.filter (fun x : ZMod p => x * (x - (N : ZMod p)) = 0)) = {0, (N : ZMod p)} := by
    ext x
    simp [mul_eq_zero, sub_eq_zero]
  rw [hset]
  split_ifs with h
  · simp [h]
  · exact Finset.card_pair (Ne.symm h)

/-- Page 89: remove the saved power from a positive binary sieve main term. -/
lemma decompJ365_lower_of_main_error {B : ℕ → ℝ} {a κ : ℝ} (ha : 0 < a) (hκ : 0 < κ) (A : ℝ)
    (hbound : ∀ᶠ n : ℕ in atTop,
      a * n / Real.log n ^ 2 - A * (n : ℝ) ^ (1 - κ) ≤ B n) :
    ∃ b : ℝ, 0 < b ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → b * n / Real.log n ^ 2 ≤ B n := by
  have hevent : ∀ᶠ n : ℕ in atTop, (a / 2) * n / Real.log n ^ 2 ≤ B n := by
    filter_upwards [hbound, decompJ365_power_error_absorb hκ ha A] with n hb he
    have heq : a * n / Real.log n ^ 2 = 2 * ((a / 2) * n / Real.log n ^ 2) := by ring
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  exact ⟨a / 2, by positivity, N, hN⟩

section PairSieve
open LeanLab.PNTSieve.Sieve SelbergSieve LeanLab.PNTSieve.SelbergSieve BoundingSieve
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1
open scoped Nat ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.omega

/-- Page 106 formula 24.5 in the second memoir: the periodic pair count
has discrepancy at most the number of roots modulo d. -/
lemma decompJ365_pair_periodic_remainder (h N d : ℕ) (hd : 0 < d) :
    |(#{m ∈ range N | d ∣ m * (m + h)} : ℝ) - (cnt h d : ℝ) * N / d| ≤ cnt h d := by
  let Q : ℕ → ℕ → Prop := fun d m => (m : ZMod d) * ((m : ZMod d) + h) = 0
  have hperiod : Function.Periodic (Q d) d := by
    intro m
    simp [Q]
  have hdiv : ∀ m : ℕ, d ∣ m * (m + h) ↔ Q d m := by
    intro m
    dsimp only [Q]
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rfl
  have hcnt : #{m ∈ range d | Q d m} = cnt h d := by
    have : NeZero d := ⟨hd.ne'⟩
    rw [card_zmod_roots]
    have h1 : #{m ∈ range d | Q d m} =
        Fintype.card {x : ZMod d // x * (x + h) = 0} := by
      rw [Fintype.card_subtype]
      refine Finset.card_bij (fun m _ => (m : ZMod d)) ?_ ?_ ?_
      · intro m hm
        simp only [mem_filter, mem_range] at hm
        simpa [Q] using hm.2
      · intro a ha b hb hab
        simp only [mem_filter, mem_range] at ha hb
        have := congrArg ZMod.val hab
        simpa [ZMod.val_cast_of_lt ha.1, ZMod.val_cast_of_lt hb.1] using this
      · intro x hx
        refine ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt x), ?_⟩,
          ZMod.natCast_zmod_val x⟩
        simp only [mem_filter, mem_univ, true_and] at hx
        simpa [Q] using hx
    rw [h1]
    refine Fintype.card_congr (Equiv.subtypeEquiv (Equiv.neg (ZMod d)) ?_)
    intro x
    simp only [Equiv.neg_apply]
    constructor
    · intro hx; linear_combination (-1 : ZMod d) * hx
    · intro hx; linear_combination (-1 : ZMod d) * hx
  have hcongr : #{m ∈ range N | d ∣ m * (m + h)} = #{m ∈ range N | Q d m} := by
    congr 1
    exact filter_congr fun m _ => hdiv m
  rw [hcongr, ← hcnt]
  exact count_periodic_approx (Q d) hd hperiod N

/-- Page 88 upper count: a Selberg estimate for any nonzero even gap.
The constant is auxiliary and is not Ricci's printed sieve constant. -/
lemma decompJ365_pair_sieve_upper (h N : ℕ) (heven : Even h) (h0 : h ≠ 0) {z : ℝ} (hz : 1 < z) :
    (#{m ∈ range N | Nat.Coprime (primorial ⌊z⌋₊) (m * (m + h))} : ℝ) ≤
      32 * N * singProd h / Real.log z ^ 2 + z * (1 + Real.log z) ^ 6 := by
  let s : SelbergSieve := {
    support := (range N).image (fun m => m * (m + h))
    prodPrimes := primorial ⌊z⌋₊
    prodPrimes_squarefree := primorial_squarefree _
    weights := fun k => (#{m ∈ range N | m * (m + h) = k} : ℝ)
    weights_nonneg := fun _ => Nat.cast_nonneg _
    totalMass := N
    nu := nuN h
    nu_mult := (nuN_compMult h).isMultiplicative
    nu_pos_of_prime := fun p hp _ => by
      rw [nuN_prime hp]; exact div_pos (wt_pos h p) (by exact_mod_cast hp.pos)
    nu_lt_one_of_prime := fun p hp _ => nuN_lt_one heven hp
    level := z
    one_le_level := hz.le }
  have hsift : siftedSum (s := s.toBoundingSieve) =
      (#{m ∈ range N | Nat.Coprime (primorial ⌊z⌋₊) (m * (m + h))} : ℝ) := by
    unfold siftedSum
    exact sum_image_fiber N (fun m => m * (m + h)) _
  have hrem : ∀ d : ℕ, Squarefree d →
      |rem (s := s.toBoundingSieve) d| ≤ 2 ^ ω d := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
    have hr : rem (s := s.toBoundingSieve) d =
        (#{m ∈ range N | d ∣ m * (m + h)} : ℝ) - nuN h d * N := by
      unfold rem multSum
      rw [show (∑ k ∈ s.support, if d ∣ k then s.weights k else 0) =
        (#{m ∈ range N | d ∣ m * (m + h)} : ℝ) from sum_image_fiber N (fun m => m * (m + h)) _]
    rw [hr]
    have hnu : nuN h d * N = (cnt h d : ℝ) * N / d := by
      rw [nuN_apply, rhoN_squarefree hd, ← cnt_squarefree hd]
      ring
    rw [hnu]
    exact (decompJ365_pair_periodic_remainder h N d hd0).trans (cnt_le_two_pow hd)
  have herr : ∑ d ∈ s.prodPrimes.divisors,
      (if (d : ℝ) ≤ z then (3 : ℝ) ^ ω d * |rem (s := s.toBoundingSieve) d| else 0) ≤
        z * (1 + Real.log z) ^ 6 := by
    have hP : Squarefree s.prodPrimes := s.prodPrimes_squarefree
    calc _ ≤ ∑ d ∈ s.prodPrimes.divisors,
          (if (d : ℝ) ≤ z then ((6 : ℕ) : ℝ) ^ ω d else 0) := by
          apply sum_le_sum
          intro d hd
          split_ifs
          · have hsq : Squarefree d := hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
            calc (3 : ℝ) ^ ω d * |rem (s := s.toBoundingSieve) d|
                ≤ 3 ^ ω d * 2 ^ ω d := by gcongr; exact hrem d hsq
              _ = ((6 : ℕ) : ℝ) ^ ω d := by rw [← mul_pow]; norm_num
          · rfl
      _ ≤ z * (1 + Real.log z) ^ 6 :=
          LeanLab.PNTSieve.Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow z hz.le hP
  have hb : Real.log z ^ 2 / (32 * singProd h) ≤ selbergBoundingSum s :=
    boundingSum_gSieve_ge h heven h0 z hz.le
  have hs := selberg_bound_simple s
  have hlog : 0 < Real.log z := Real.log_pos hz
  have hsp := singProd_pos h
  have hlow : 0 < Real.log z ^ 2 / (32 * singProd h) := by positivity
  have hmain : (N : ℝ) / selbergBoundingSum s ≤
      (N : ℝ) / (Real.log z ^ 2 / (32 * singProd h)) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) hlow hb
  have heq : (N : ℝ) / (Real.log z ^ 2 / (32 * singProd h)) =
      32 * N * singProd h / Real.log z ^ 2 := by field_simp
  rw [hsift] at hs
  change _ ≤ (N : ℝ) / selbergBoundingSum s + _ at hs
  linarith
end PairSieve

/-- Page 88: a rough pair is coprime to the small prime product. -/
lemma decompJ365_rough_coprime {x h : ℕ} {z : ℝ} (hz : 0 ≤ z) (hx : 0 < x)
    (hxrough : ∀ p ∈ x.primeFactorsList, z < (p : ℝ))
    (hhrough : ∀ p ∈ (x + h).primeFactorsList, z < (p : ℝ)) :
    Nat.Coprime (primorial ⌊z⌋₊) (x * (x + h)) := by
  by_contra hc
  obtain ⟨p, hp, hpP, hpX⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  have hpz : p ≤ ⌊z⌋₊ := (LeanLab.PNTSieve.Sieve.prime_dvd_primorial_iff _ _ hp).mp hpP
  rcases hp.dvd_mul.mp hpX with hpx | hph
  · have hr := hxrough p ((Nat.mem_primeFactorsList (by omega : x ≠ 0)).mpr ⟨hp, hpx⟩)
    have hf : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le hz
    have hpr : (p : ℝ) ≤ ⌊z⌋₊ := by exact_mod_cast hpz
    linarith
  · have hr := hhrough p ((Nat.mem_primeFactorsList (by omega : x + h ≠ 0)).mpr ⟨hp, hph⟩)
    have hf : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le hz
    have hpr : (p : ℝ) ≤ ⌊z⌋₊ := by exact_mod_cast hpz
    linarith

open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1
open LeanLab.PNTSieve.Sieve

/-- Page 88 upper count at a power cutoff, with an auxiliary explicit constant. -/
lemma decompJ365_power_cutoff_upper (h : ℕ) (heven : Even h) (h0 : h ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2) {N : ℕ} (hN : 2 ≤ N) :
    (#{m ∈ range (N + 1) | Nat.Coprime (primorial ⌊(N : ℝ) ^ δ⌋₊) (m * (m + h))} : ℝ) ≤
      (64 * singProd h / δ ^ 2 + 17 ^ 8) * N / Real.log N ^ 2 := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hNr1 : (1 : ℝ) ≤ N := hNr.le
  have hz : 1 < (N : ℝ) ^ δ := Real.one_lt_rpow hNr hδ
  have hlog : 0 < Real.log N := Real.log_pos hNr
  have hlogz : Real.log ((N : ℝ) ^ δ) = δ * Real.log N := Real.log_rpow (by positivity) _
  have hraw := decompJ365_pair_sieve_upper h (N + 1) heven h0 hz
  have hsp := singProd_pos h
  have hNp : ((N + 1 : ℕ) : ℝ) ≤ 2 * N := by push_cast; linarith
  have hmain : 32 * (N + 1 : ℕ) * singProd h / Real.log ((N : ℝ) ^ δ) ^ 2 ≤
      (64 * singProd h / δ ^ 2) * N / Real.log N ^ 2 := by
    calc
      _ = (32 * singProd h / δ ^ 2) * (((N + 1 : ℕ) : ℝ) / Real.log N ^ 2) := by
        rw [hlogz]
        field_simp
      _ ≤ (32 * singProd h / δ ^ 2) * (2 * N / Real.log N ^ 2) := by gcongr
      _ = _ := by ring
  have hzsqrt : (N : ℝ) ^ δ ≤ Real.sqrt N := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hNr1 hδhalf
  have hzN : (N : ℝ) ^ δ ≤ N := by
    calc _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNr1 (by linarith)
         _ = _ := Real.rpow_one _
  have hlogle : Real.log ((N : ℝ) ^ δ) ≤ Real.log N := Real.log_le_log (by positivity) hzN
  have herr : (N : ℝ) ^ δ * (1 + Real.log ((N : ℝ) ^ δ)) ^ 6 ≤
      (17 : ℝ) ^ 8 * N / Real.log N ^ 2 := by
    calc
      _ ≤ Real.sqrt N * (1 + Real.log N) ^ 6 := by
        apply mul_le_mul hzsqrt
          (pow_le_pow_left₀ (by linarith [Real.log_pos hz]) (by linarith) 6)
          (by positivity) (by positivity)
      _ ≤ _ := (le_div_iff₀ (sq_pos_of_pos hlog)).mpr (polylog_bound N hNr1)
  have halg : (64 * singProd h / δ ^ 2 + 17 ^ 8) * (N : ℝ) / Real.log N ^ 2 =
      (64 * singProd h / δ ^ 2) * N / Real.log N ^ 2 + 17 ^ 8 * N / Real.log N ^ 2 := by ring
  rw [halg]
  exact hraw.trans (add_le_add hmain herr)

/-- Page 88 variable thresholds: discard the initial square root segment. -/
lemma decompJ365_variable_rough_cutoff (h ξ : ℕ) {α β δ : ℝ} (hξ : 1 ≤ ξ) (hα : 0 < α) (hβ : 0 < β)
    (hδα : δ ≤ α / 2) (hδβ : δ ≤ β / 2)
 :
    #{x ∈ Icc (1 : ℕ) ξ |
      (∀ p : ℕ, p ∈ x.primeFactorsList → ((x : ℕ) : ℝ) ^ α < (p : ℝ)) ∧
      ∀ p : ℕ, p ∈ (x + h).primeFactorsList → ((x : ℕ) : ℝ) ^ β < (p : ℝ)} ≤
      ⌊(ξ : ℝ) ^ ((1 : ℝ) / 2)⌋₊ +
        #{x ∈ range (ξ + 1) | Nat.Coprime (primorial ⌊(ξ : ℝ) ^ δ⌋₊) (x * (x + h))} := by
  let T := ⌊(ξ : ℝ) ^ ((1 : ℝ) / 2)⌋₊
  have hξr : (1 : ℝ) ≤ ξ := by exact_mod_cast hξ
  have hsub : {x ∈ Icc (1 : ℕ) ξ |
      (∀ p : ℕ, p ∈ x.primeFactorsList → ((x : ℕ) : ℝ) ^ α < (p : ℝ)) ∧
      ∀ p : ℕ, p ∈ (x + h).primeFactorsList → ((x : ℕ) : ℝ) ^ β < (p : ℝ)} ⊆
      Icc 1 T ∪ {x ∈ range (ξ + 1) | Nat.Coprime (primorial ⌊(ξ : ℝ) ^ δ⌋₊) (x * (x + h))} := by
    intro x hx
    rcases mem_filter.mp hx with ⟨hxI, hxp, hhp⟩
    rcases mem_Icc.mp hxI with ⟨hx1, hxξ⟩
    by_cases hsmall : x ≤ T
    · exact mem_union_left _ (mem_Icc.mpr ⟨hx1, hsmall⟩)
    · apply mem_union_right
      refine mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩
      have hlarge : (ξ : ℝ) ^ ((1 : ℝ) / 2) < x :=
        (Nat.floor_lt (by positivity)).mp (by omega : T < x)
      have hpow : ∀ γ : ℝ, 0 < γ → δ ≤ γ / 2 → (ξ : ℝ) ^ δ ≤ ((x : ℕ) : ℝ) ^ γ := by
        intro γ hγ hδγ
        calc _ ≤ (ξ : ℝ) ^ (γ / 2) := Real.rpow_le_rpow_of_exponent_le hξr hδγ
             _ = ((ξ : ℝ) ^ ((1 : ℝ) / 2)) ^ γ := by
               rw [← Real.rpow_mul (by positivity)]; congr 1; ring
             _ ≤ ((x : ℕ) : ℝ) ^ γ := Real.rpow_le_rpow (by positivity) hlarge.le hγ.le
      exact decompJ365_rough_coprime (by positivity) (by omega) (fun p hp => (hpow α hα hδα).trans_lt (hxp p hp))
        (fun p hp => (hpow β hβ hδβ).trans_lt (hhp p hp))
  exact (card_le_card hsub).trans ((card_union_le _ _).trans_eq (by simp [T]))

/-- Page 88 upper count for two linear polynomials at any positive roughness powers. -/
lemma decompJ365_rough_pair_upper (h : ℕ) (heven : Even h) (h0 : h ≠ 0) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
 :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℕ, 2 ≤ ξ →
      (#{x ∈ Icc (1 : ℕ) ξ |
        (∀ p : ℕ, p ∈ x.primeFactorsList → ((x : ℕ) : ℝ) ^ α < (p : ℝ)) ∧
        ∀ p : ℕ, p ∈ (x + h).primeFactorsList → ((x : ℕ) : ℝ) ^ β < (p : ℝ)} : ℝ) ≤
          C * ξ / Real.log ξ ^ 2 := by
  let δ : ℝ := min (min (α / 2) (β / 2)) (1 / 2)
  have hδ : 0 < δ := lt_min (lt_min (by positivity) (by positivity)) (by norm_num)
  have hδa : δ ≤ α / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδb : δ ≤ β / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hsp := singProd_pos h
  refine ⟨64 * singProd h / δ ^ 2 + 2 * 17 ^ 8, by positivity, ?_⟩
  intro ξ hξ
  have hξr : (1 : ℝ) < ξ := by exact_mod_cast (by omega : 1 < ξ)
  have hlog : 0 < Real.log ξ := Real.log_pos hξr
  have hmain := decompJ365_power_cutoff_upper h heven h0 hδ hδhalf hξ
  have hcount : (#{x ∈ Icc (1 : ℕ) ξ |
        (∀ p : ℕ, p ∈ x.primeFactorsList → ((x : ℕ) : ℝ) ^ α < (p : ℝ)) ∧
        ∀ p : ℕ, p ∈ (x + h).primeFactorsList → ((x : ℕ) : ℝ) ^ β < (p : ℝ)} : ℝ) ≤
      (⌊(ξ : ℝ) ^ ((1 : ℝ) / 2)⌋₊ : ℝ) +
        #{x ∈ range (ξ + 1) | Nat.Coprime (primorial ⌊(ξ : ℝ) ^ δ⌋₊) (x * (x + h))} := by
    exact_mod_cast decompJ365_variable_rough_cutoff h ξ (by omega) hα hβ hδa hδb
  have hfloor : (⌊(ξ : ℝ) ^ ((1 : ℝ) / 2)⌋₊ : ℝ) ≤ Real.sqrt ξ := by
    rw [Real.sqrt_eq_rpow]
    exact Nat.floor_le (by positivity)
  have hpoly := polylog_bound ξ hξr.le
  have hfactor : 1 ≤ (1 + Real.log (ξ : ℝ)) ^ 6 := one_le_pow₀ (by linarith)
  have hsqrt : Real.sqrt ξ ≤ (17 : ℝ) ^ 8 * ξ / Real.log ξ ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hlog)).mpr
    have hle := mul_le_mul_of_nonneg_left hfactor
      (mul_nonneg (Real.sqrt_nonneg (ξ : ℝ)) (sq_nonneg (Real.log (ξ : ℝ))))
    nlinarith
  have halg : (64 * singProd h / δ ^ 2 + 2 * 17 ^ 8) * (ξ : ℝ) / Real.log ξ ^ 2 =
      (64 * singProd h / δ ^ 2 + 17 ^ 8) * ξ / Real.log ξ ^ 2 +
        17 ^ 8 * ξ / Real.log ξ ^ 2 := by ring
  rw [halg]
  linarith

/-- Page 88: forget the factor counts for a nonnegative shift. -/
lemma decompJ365_zCount_nonneg_le_rough (a b h ξ : ℕ) (m : ℤ) (hm : (h : ℤ) = 2 * m) : zCount a b m ξ ≤
    #{x ∈ Icc (1 : ℕ) ξ |
      (∀ p : ℕ, p ∈ x.primeFactorsList → ((x : ℕ) : ℝ) ^ (1 / ((a : ℝ) + 1)) < (p : ℝ)) ∧
      ∀ p : ℕ, p ∈ (x + h).primeFactorsList → ((x : ℕ) : ℝ) ^ (1 / ((b : ℝ) + 1)) < (p : ℝ)} := by
  classical
  unfold zCount
  apply card_le_card
  intro x hx
  rcases mem_filter.mp hx with ⟨hxI, hfirst, hpos, hsecond⟩
  simp only [mem_filter]
  refine ⟨hxI, ?_⟩
  constructor
  · exact hfirst.2.2
  · have heq : ((x : ℤ) + 2 * m).toNat = x + h := by omega
    intro p hp
    exact hsecond.2.2 p (by simpa only [heq] using hp)

/-- Page 88: translate a negative shift injectively and exchange the two powers. -/
lemma decompJ365_zCount_negative_le_rough (a b h ξ : ℕ) (m : ℤ) (hm : (h : ℤ) = -2 * m) : zCount a b m ξ ≤
    #{x ∈ Icc (1 : ℕ) ξ |
      (∀ p : ℕ, p ∈ x.primeFactorsList → ((x : ℕ) : ℝ) ^ (1 / ((b : ℝ) + 1)) < (p : ℝ)) ∧
      ∀ p : ℕ, p ∈ (x + h).primeFactorsList → ((x : ℕ) : ℝ) ^ (1 / ((a : ℝ) + 1)) < (p : ℝ)} := by
  classical
  unfold zCount
  let f : ℕ → ℕ := fun x => ((x : ℤ) + 2 * m).toNat
  apply card_le_card_of_injOn f
  · intro x hx
    rcases mem_filter.mp hx with ⟨hxI, hfirst, hpos, hsecond⟩
    rcases mem_Icc.mp hxI with ⟨hx1, hxξ⟩
    have hf : (f x : ℤ) = (x : ℤ) + 2 * m := Int.toNat_of_nonneg hpos.le
    have hfx : f x ≤ x := by omega
    have hfxr : (f x : ℝ) ≤ x := by exact_mod_cast hfx
    have hx_eq : f x + h = x := by omega
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨by omega, by omega⟩, ?_, ?_⟩
    · intro p hp
      exact (Real.rpow_le_rpow (by positivity) hfxr (by positivity)).trans_lt (hsecond.2.2 p hp)
    · rw [hx_eq]
      intro p hp
      exact (Real.rpow_le_rpow (by positivity) hfxr (by positivity)).trans_lt (hfirst.2.2 p hp)
  · intro x hx y hy hxy
    have hpx := (mem_filter.mp hx).2.2.1
    have hpy := (mem_filter.mp hy).2.2.1
    have hfx : (f x : ℤ) = (x : ℤ) + 2 * m := Int.toNat_of_nonneg hpx.le
    have hfy : (f y : ℤ) = (y : ℤ) + 2 * m := Int.toNat_of_nonneg hpy.le
    have : (f x : ℤ) = f y := by exact_mod_cast hxy
    omega

/-- Page 88: the full upper half of Theorem DZ, for every nonzero integer shift. -/
lemma decompJ365_zCount_upper (a b : ℕ) (m : ℤ) (hm : m ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℕ, 2 ≤ ξ → (zCount a b m ξ : ℝ) ≤ C * ξ / Real.log ξ ^ 2 := by
  rcases lt_or_gt_of_ne hm with hmneg | hmpos
  · let n := (-m).toNat
    have hncast : (n : ℤ) = -m := Int.toNat_of_nonneg (by omega)
    have hnpos : 0 < n := by omega
    have hhcast : ((2 * n : ℕ) : ℤ) = -2 * m := by push_cast; omega
    obtain ⟨C, hC, hupper⟩ := decompJ365_rough_pair_upper (2 * n) (even_two_mul n)
      (by omega) (by positivity : (0 : ℝ) < 1 / ((b : ℝ) + 1))
      (by positivity : (0 : ℝ) < 1 / ((a : ℝ) + 1))
    refine ⟨C, hC, fun ξ hξ => le_trans ?_ (hupper ξ hξ)⟩
    exact_mod_cast decompJ365_zCount_negative_le_rough a b (2 * n) ξ m hhcast
  · let n := m.toNat
    have hncast : (n : ℤ) = m := Int.toNat_of_nonneg hmpos.le
    have hnpos : 0 < n := by omega
    obtain ⟨C, hC, hupper⟩ := decompJ365_rough_pair_upper (2 * n) (even_two_mul n)
      (by omega) (by positivity : (0 : ℝ) < 1 / ((a : ℝ) + 1))
      (by positivity : (0 : ℝ) < 1 / ((b : ℝ) + 1))
    refine ⟨C, hC, fun ξ hξ => le_trans ?_ (hupper ξ hξ)⟩
    have hhcast : ((2 * n : ℕ) : ℤ) = 2 * m := by push_cast; omega
    exact_mod_cast decompJ365_zCount_nonneg_le_rough a b (2 * n) ξ m hhcast

/-- CONDITIONAL ON the positive lower count. The Z upper estimate is proved above. -/
lemma decompJ365_Z_of_lower {a b : ℕ}
    (hlower : ∀ m : ℤ, m ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℕ, ∀ ξ : ℕ, ξ₀ ≤ ξ →
      c * ξ / Real.log ξ ^ 2 ≤ zCount a b m ξ) : TheoremDZ a b := by
  intro m hm
  obtain ⟨c, hc, ξ₀, hl⟩ := hlower m hm
  obtain ⟨C, hC, hu⟩ := decompJ365_zCount_upper a b m hm
  exact ⟨c, C, hc, hC, max 2 ξ₀, fun ξ hξ => ⟨hl ξ (by omega), hu ξ (by omega)⟩⟩

/-- Page 89 case two: the displayed modified tau is below 2.43. -/
lemma decompJ365_tau_case2 : exp (-(log (4 / 3 : ℝ)) / 2) * ricciTau 2 < 2.43 := by
  have heq : exp (-(log (4 / 3 : ℝ)) / 2) ^ 2 = (3 / 4 : ℝ) := by
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (-(log (4 / 3 : ℝ)) / 2) = -log (4 / 3 : ℝ) by ring,
      exp_neg, exp_log (by norm_num)]
    norm_num
  have hepos := exp_pos (-(log (4 / 3 : ℝ)) / 2)
  have he : exp (-(log (4 / 3 : ℝ)) / 2) < 0.8661 := by nlinarith
  have hprod := mul_lt_mul_of_pos_left ricciTau_two_lt hepos
  nlinarith

/-- Page 89 case three: the displayed modified tau is below 1.98. -/
lemma decompJ365_tau_case3 : exp (-(log (2 : ℝ)) / 2) * ricciTau 2 < 1.98 := by
  have heq : exp (-(log (2 : ℝ)) / 2) ^ 2 = (1 / 2 : ℝ) := by
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (-(log (2 : ℝ)) / 2) = -log (2 : ℝ) by ring,
      exp_neg, exp_log (by norm_num)]
    norm_num
  have hepos := exp_pos (-(log (2 : ℝ)) / 2)
  have he : exp (-(log (2 : ℝ)) / 2) < 0.7072 := by nlinarith
  have hprod := mul_lt_mul_of_pos_left ricciTau_two_lt hepos
  nlinarith

/-- Page 89 case four: the displayed modified tau is below 1.49. -/
lemma decompJ365_tau_case4 : exp (-0.90 : ℝ) + exp (-(log (4 : ℝ)) / 2) *
    (exp (-1.46 / 2) + exp (-1.98 / 2) / (1 - exp (-0.50 / 2))) < 1.49 := by
  have heq : exp (-(log (4 : ℝ)) / 2) = (1 / 2 : ℝ) := by
    have he : exp (-(log (4 : ℝ)) / 2) ^ 2 = (1 / 4 : ℝ) := by
      rw [← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [show (2 : ℝ) * (-(log (4 : ℝ)) / 2) = -log (4 : ℝ) by ring,
        exp_neg, exp_log (by norm_num)]
      norm_num
    nlinarith [exp_pos (-(log (4 : ℝ)) / 2)]
  have h09 : exp (-0.9) ≤ 1 / 2.4596 := ricci_exp_neg_upper (by norm_num)
    (ricci_exp_lower (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  have h045 : 1 / (1.568313 : ℝ) ≤ exp (-0.45) := by
    rw [exp_neg, one_div]
    apply inv_anti₀ (exp_pos _)
    exact ricci_exp_upper_small (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have ht := ricciTau_two_lt
  norm_num [ricciTau] at ht
  rw [heq]
  norm_num
  linarith

/-- Page 88: the two dimensional prime product has a positive log squared lower bound.
The explicit constant exp of negative 52 is auxiliary. -/
lemma decompJ365_prime_product_lower (z : ℕ) (hz : 3 ≤ z) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ 3 ≤ p ∧ p ≤ z) :
    exp (-52 : ℝ) / Real.log z ^ 2 ≤ ∏ p ∈ S, (1 - (2 : ℝ) / p) := by
  have hzR : (3 : ℝ) ≤ z := by exact_mod_cast hz
  have hlog : 0 < Real.log z := Real.log_pos (by linarith)
  have hsub : S ⊆ (Icc 1 z).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpr, h3, hpz⟩ := hS p hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hpz⟩, hpr⟩
  have hpos : ∀ p ∈ (Icc 1 z).filter Nat.Prime, 0 ≤ 1 - (1 : ℝ) / p := by
    intro p hp
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.two_le
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hpR
    linarith
  have hsubsetprod : (∏ p ∈ (Icc 1 z).filter Nat.Prime, (1 - (1 : ℝ) / p)) ≤
      ∏ p ∈ S, (1 - (1 : ℝ) / p) :=
    prod_le_prod_of_subset_of_le_one₀ hsub hpos (fun p hp _ => by
      have hi : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
      linarith)
  have hfirst := (mertens_product_ge z (by omega)).trans hsubsetprod
  have hsecond := prod_one_sub_inv_pred_ge z hz S hS
  have hfirst0 : 0 ≤ exp (-16 : ℝ) / Real.log z := by positivity
  have hsecond0 : 0 ≤ ∏ p ∈ S, (1 - (1 : ℝ) / ((p : ℝ) - 1)) := by
    exact (by positivity : (0 : ℝ) ≤ exp (-36 : ℝ) / Real.log z).trans hsecond
  have hmul := mul_le_mul hfirst hsecond (by positivity) (hfirst0.trans hfirst)
  have hid : ∀ p ∈ S, (1 - (1 : ℝ) / p) * (1 - (1 : ℝ) / ((p : ℝ) - 1)) =
      1 - (2 : ℝ) / p := by
    intro p hp
    have hpR : (3 : ℝ) ≤ p := by exact_mod_cast (hS p hp).2.1
    field_simp [ne_of_gt (show (0 : ℝ) < p by linarith),
      ne_of_gt (show (0 : ℝ) < (p : ℝ) - 1 by linarith)]
    ring
  have hprod : (∏ p ∈ S, (1 - (1 : ℝ) / p)) *
      (∏ p ∈ S, (1 - (1 : ℝ) / ((p : ℝ) - 1))) = ∏ p ∈ S, (1 - (2 : ℝ) / p) := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl hid
  rw [hprod] at hmul
  have heq : exp (-16 : ℝ) / Real.log z * (exp (-36 : ℝ) / Real.log z) =
      exp (-52 : ℝ) / Real.log z ^ 2 := by
    rw [div_mul_div_comm, ← exp_add]
    norm_num [pow_two]
  rwa [heq] at hmul

/-- Page 89: epsilon equal to 0.001 leaves strict exponent margins for all first four pairs. -/
lemma decompJ365_first_four_margins :
    let t₂ := exp (-(log (4 / 3 : ℝ)) / 2) * ricciTau 2
    let t₃ := exp (-(log (2 : ℝ)) / 2) * ricciTau 2
    let t₄ := exp (-0.90 : ℝ) + exp (-(log (4 : ℝ)) / 2) *
      (exp (-1.46 / 2) + exp (-1.98 / 2) / (1 - exp (-0.50 / 2)))
    (1 + 2 * ricciTau 2 + 2 * 0.001 < 7) ∧
    (1 + 2 * t₂ + 2 * 0.001 < 6 ∧ (4 / 3 : ℝ) * (1 + 2 * t₂ + 2 * 0.001) < 8) ∧
    (1 + 2 * t₃ + 2 * 0.001 < 5 ∧ (2 : ℝ) * (1 + 2 * t₃ + 2 * 0.001) < 10) ∧
    (1 + 2 * t₄ + 2 * 0.001 < 4 ∧ (4 : ℝ) * (1 + 2 * t₄ + 2 * 0.001) < 16) := by
  dsimp only
  have h1 := ricciTau_two_lt
  have h2 := decompJ365_tau_case2
  have h3 := decompJ365_tau_case3
  have h4 := decompJ365_tau_case4
  refine ⟨by linarith, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
    ⟨by linarith, by linarith⟩⟩

/-- Page 89: the three positive omega choices lie in their stated parameter windows. -/
lemma decompJ365_omega_windows : (0 < log (4 / 3 : ℝ) ∧ log (4 / 3 : ℝ) < 0.90) ∧
    (0 < log (2 : ℝ) ∧ log (2 : ℝ) < 0.90) ∧
    ((0.90 : ℝ) < log (4 : ℝ) ∧ log (4 : ℝ) < 1.46) := by
  have he09 : (2.4596 : ℝ) ≤ exp 0.90 := ricci_exp_lower (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have he09u : exp (0.90 : ℝ) ≤ 2.46 := ricci_exp_upper_small (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have he146 : (4.3055 : ℝ) ≤ exp 1.46 := ricci_exp_lower (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])
  refine ⟨⟨log_pos (by norm_num), (log_lt_iff_lt_exp (by norm_num)).mpr (by linarith)⟩,
    ⟨log_pos (by norm_num), (log_lt_iff_lt_exp (by norm_num)).mpr (by linarith)⟩,
    (lt_log_iff_exp_lt (by norm_num)).mpr (by linarith),
    (log_lt_iff_lt_exp (by norm_num)).mpr (by linarith)⟩

/-- Page 89: the strict exponent margin turns a size bound into the required prime threshold. -/
lemma decompJ365_threshold_lt_of_power {N R u : ℝ} {a : ℕ} (hN : 0 ≤ N) (hR : 1 ≤ R)
    (hu : u < a + 1) (hsize : N < R ^ u) :
    N ^ (1 / ((a : ℝ) + 1)) < R := by
  have hle : R ^ u ≤ R ^ (a + 1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR hu.le
  have hlt : N < R ^ (a + 1 : ℝ) := hsize.trans_le hle
  rw [one_div]
  exact (Real.rpow_inv_lt_iff_of_pos hN (by linarith) (by positivity)).mpr hlt

/-- Page 89: Bertrand supplies an eventual prime cutoff between any two positive power exponents. -/
lemma decompJ365_prime_cutoff {u ε : ℝ} (hu : 0 < u) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ (p : ℝ) ^ u ≤ N ∧ (N : ℝ) < (p : ℝ) ^ (u + ε) := by
  let v : ℝ := 1 / (u + ε / 2)
  have hden : 0 < u + ε / 2 := by positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hvu : v * u < 1 := by
    dsimp [v]
    rw [one_div_mul_eq_div, div_lt_one hden]
    linarith
  have hvue : 1 < v * (u + ε) := by
    dsimp [v]
    rw [one_div_mul_eq_div, one_lt_div hden]
    linarith
  have hκ : 0 < 1 - v * u := by linarith
  have hgrowth : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - v * u)) atTop atTop :=
    (tendsto_rpow_atTop hκ).comp tendsto_natCast_atTop_atTop
  filter_upwards [hgrowth.eventually (eventually_ge_atTop ((2 : ℝ) ^ u)),
    eventually_ge_atTop 2] with N hNgrowth hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hroot1 : 1 ≤ (N : ℝ) ^ v := Real.one_le_rpow hNr.le hv.le
  have hfloor : 1 ≤ ⌊(N : ℝ) ^ v⌋₊ := Nat.le_floor (by simpa using hroot1)
  obtain ⟨p, hp, hpl, hpu⟩ := Nat.exists_prime_lt_and_le_two_mul ⌊(N : ℝ) ^ v⌋₊ (by omega)
  have hplr : (N : ℝ) ^ v < p := (Nat.floor_lt (by positivity)).mp hpl
  have hpur : (p : ℝ) ≤ 2 * (N : ℝ) ^ v := by
    have hcast : (p : ℝ) ≤ 2 * (⌊(N : ℝ) ^ v⌋₊ : ℝ) := by exact_mod_cast hpu
    exact hcast.trans (mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (by norm_num))
  refine ⟨p, hp, ?_, ?_⟩
  · calc
      (p : ℝ) ^ u ≤ (2 * (N : ℝ) ^ v) ^ u := Real.rpow_le_rpow (by positivity) hpur hu.le
      _ = (2 : ℝ) ^ u * (N : ℝ) ^ (v * u) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by positivity)]
      _ ≤ (N : ℝ) ^ (1 - v * u) * (N : ℝ) ^ (v * u) :=
        mul_le_mul_of_nonneg_right hNgrowth (by positivity)
      _ = N := by rw [← Real.rpow_add (by linarith)]; norm_num
  · calc
      (N : ℝ) < (N : ℝ) ^ (v * (u + ε)) := by
        simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hNr hvue
      _ = ((N : ℝ) ^ v) ^ (u + ε) := Real.rpow_mul (by positivity) _ _
      _ < (p : ℝ) ^ (u + ε) := Real.rpow_lt_rpow (by positivity) hplr (by positivity)

/-- Pages 74 and 88: the two linear factor product is outside the irreducible C hypotheses. -/
lemma decompJ365_product_not_CHyp (m : ℤ) : ¬ CHyp ((Polynomial.X : Polynomial ℤ) * (Polynomial.X + Polynomial.C (2 * m))) := by
  intro hp
  have hirr := hp.2.2.1
  have hu := hirr.isUnit_or_isUnit rfl
  exact hu.elim Polynomial.not_isUnit_X (Polynomial.not_isUnit_X_add_C (2 * m))

/-- Negative route check for page 88: the first unweighted Brun main coefficient
is already negative once both odd primes three and five are included. -/
lemma decompJ365_first_brun_main_negative (S : Finset ℕ) (h3 : 3 ∈ S) (h5 : 5 ∈ S) :
    1 - ∑ p ∈ S, (2 : ℝ) / p < 0 := by
  have hsub : ({3, 5} : Finset ℕ) ⊆ S := by
    intro p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact h3
    · exact h5
  have hsum := sum_le_sum_of_subset_of_nonneg hsub (f := fun p : ℕ => (2 : ℝ) / p)
    (fun p _ _ => by positivity)
  norm_num at hsum
  linarith

/-- Negative route check for page 89: a one twenty first roughness power
and at most six factors do not imply the required one seventh roughness power. -/
lemma decompJ365_weak_roughness_not_enough : AlmostGT 6 ((3027 : ℝ) ^ ((1 : ℝ) / 21)) 3027 ∧
    ¬ AlmostGT 6 ((3027 : ℝ) ^ ((1 : ℝ) / 7)) 3027 := by
  have hf : Nat.primeFactorsList 3027 = [3, 1009] := by norm_num
  have hweak : (3027 : ℝ) ^ ((1 : ℝ) / 21) < 3 := by
    rw [one_div, Real.rpow_inv_lt_iff_of_pos (by norm_num) (by norm_num) (by norm_num),
      Real.rpow_ofNat]
    norm_num
  have hstrong : (3 : ℝ) < (3027 : ℝ) ^ ((1 : ℝ) / 7) := by
    rw [one_div, Real.lt_rpow_inv_iff_of_pos (by norm_num) (by norm_num) (by norm_num),
      Real.rpow_ofNat]
    norm_num
  constructor
  · refine ⟨by norm_num, by simp [hf], ?_⟩
    intro p hp
    simp only [hf, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hweak
    · linarith
  · intro hh
    have := hh.2.2 3 (by simp [hf])
    linarith

open LeanLab.PNTSieve.Bonferroni

/-- Second memoir page 107: an odd Brun truncation bounds the finite pair survivor count below. -/
lemma decompJ365_pair_brun_lower (h N : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {r : ℕ} (hr : Odd r) :
    (∑ T ∈ P.powerset.filter (fun T => T.card ≤ r), (-1 : ℝ) ^ T.card *
      (#{m ∈ range N | (∏ p ∈ T, p) ∣ m * (m + h)} : ℝ)) ≤
      #{m ∈ range N | ∀ p ∈ P, ¬ p ∣ m * (m + h)} := by
  have hinj : Function.Injective (fun m : ℕ => m * (m + h)) := by
    intro x y hxy
    rcases lt_trichotomy x y with hl | rfl | hl
    · nlinarith
    · rfl
    · nlinarith
  have hcard (Q : ℕ → Prop) [DecidablePred Q] :
      #(((range N).image (fun m => m * (m + h))).filter Q) =
      #{m ∈ range N | Q (m * (m + h))} := by
    rw [filter_image, card_image_of_injective _ hinj]
  have hraw := brun_lower ((range N).image (fun m => m * (m + h))) P hP hr
  unfold brunSum sifted at hraw
  simp only [hcard] at hraw
  exact_mod_cast hraw

/-- Second memoir pages 106 and 107: substitute the local root densities and bound every finite remainder. -/
lemma decompJ365_pair_brun_lower_explicit (h N : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {r : ℕ} (hr : Odd r) :
    (∑ T ∈ P.powerset.filter (fun T => T.card ≤ r),
      (-1 : ℝ) ^ T.card * ((cnt h (∏ p ∈ T, p) : ℝ) * N / (∏ p ∈ T, p))) -
      (∑ T ∈ P.powerset.filter (fun T => T.card ≤ r), (cnt h (∏ p ∈ T, p) : ℝ)) ≤ #{m ∈ range N | ∀ p ∈ P, ¬ p ∣ m * (m + h)} := by
  have hterm : ∀ T ∈ P.powerset.filter (fun T => T.card ≤ r),
      (-1 : ℝ) ^ T.card * ((cnt h (∏ p ∈ T, p) : ℝ) * N / (∏ p ∈ T, p)) -
        cnt h (∏ p ∈ T, p) ≤
      (-1 : ℝ) ^ T.card * (#{m ∈ range N | (∏ p ∈ T, p) ∣ m * (m + h)} : ℝ) := by
    intro T hT
    have hTP : T ⊆ P := mem_powerset.mp (mem_filter.mp hT).1
    have hd : 0 < ∏ p ∈ T, p := prod_pos (fun p hp => (hP p (hTP hp)).pos)
    have hrem := decompJ365_pair_periodic_remainder h N (∏ p ∈ T, p) hd
    have herr : |(-1 : ℝ) ^ T.card *
        ((#{m ∈ range N | (∏ p ∈ T, p) ∣ m * (m + h)} : ℝ) -
          (cnt h (∏ p ∈ T, p) : ℝ) * N / (∏ p ∈ T, p))| ≤ cnt h (∏ p ∈ T, p) := by
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using hrem
    have hlo := (abs_le.mp herr).1
    nlinarith
  simpa only [sum_sub_distrib] using (sum_le_sum hterm).trans (decompJ365_pair_brun_lower h N P hP hr)

/-- Second memoir pages 106 and 107: the pure finite Brun lower estimate
with the local density product, factorial truncation error and explicit arithmetic remainder. -/
lemma decompJ365_pair_brun_product_lower (h N : ℕ) (heven : Even h) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {r : ℕ} (hr : Odd r) :
    (N : ℝ) * (∏ p ∈ P, (1 - nuN h p)) -
      N * ((∑ p ∈ P, nuN h p) ^ (r + 1) / ((r + 1).factorial : ℝ)) -
      (∑ T ∈ P.powerset.filter (fun T => T.card ≤ r),
        (LeanLab.SchnirelmannGoldbach.S1.cnt h (∏ p ∈ T, p) : ℝ)) ≤
      #{m ∈ range N | ∀ p ∈ P, ¬ p ∣ m * (m + h)} := by
  let f : ℕ → ℝ := fun p => if p.Prime then nuN h p else 0
  have hf0 : ∀ p, 0 ≤ f p := by
    intro p
    dsimp [f]
    split_ifs
    · exact nuN_nonneg h p
    · rfl
  have hf1 : ∀ p, f p ≤ 1 := by
    intro p
    dsimp [f]
    split_ifs with hp
    · exact (nuN_lt_one heven hp).le
    · norm_num
  have hfP : ∀ p ∈ P, f p = nuN h p := fun p hp => ite_eq_left (hP p hp)
  have hdensity : ∀ T : Finset ℕ, T ⊆ P →
      (LeanLab.SchnirelmannGoldbach.S1.cnt h (∏ p ∈ T, p) : ℝ) / (∏ p ∈ T, p) = ∏ p ∈ T, f p := by
    intro T hT
    rw [cnt_prod_primes h T (fun p hp => hP p (hT hp)), Nat.cast_prod, ← prod_div_distrib]
    apply prod_congr rfl
    intro p hp
    rw [hfP p (hT hp), nuN_prime (hP p (hT hp))]
  have hsum :
      (∑ T ∈ P.powerset.filter (fun T => T.card ≤ r), (-1 : ℝ) ^ T.card *
        ((LeanLab.SchnirelmannGoldbach.S1.cnt h (∏ p ∈ T, p) : ℝ) * N / (∏ p ∈ T, p))) =
      N * (∑ T ∈ P.powerset.filter (fun T => T.card ≤ r), (-1 : ℝ) ^ T.card * ∏ p ∈ T, f p) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro T hT
    rw [← hdensity T (mem_powerset.mp (mem_filter.mp hT).1)]
    ring
  have hraw := decompJ365_pair_brun_lower_explicit h N P hP hr
  rw [hsum] at hraw
  have hmain := (abs_le.mp (main_dev P f hf0 hf1 r)).1
  have hmul := mul_le_mul_of_nonneg_left hmain (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hprod : (∏ p ∈ P, (1 - f p)) = ∏ p ∈ P, (1 - nuN h p) :=
    prod_congr rfl (fun p hp => by rw [hfP p hp])
  have hlinear : (∑ p ∈ P, f p) = ∑ p ∈ P, nuN h p := sum_congr rfl hfP
  rw [hprod, hlinear] at hmul
  linarith

/-- Second memoir pages 106 and 107, auxiliary weight sum for indexed values.
Repeated values retain their index multiplicity. -/
lemma decompJ365_indexed_weight_sum (I Ω : Finset ℕ) (F : ℕ → ℕ) (c : Finset ℕ → ℝ) :
    ∑ i ∈ I, wEval Ω c (F i) =
      ∑ S ∈ Ω.powerset, c S * (#{i ∈ I | (∏ p ∈ S, p) ∣ F i} : ℝ) := by
  unfold wEval ind
  rw [sum_comm]
  apply sum_congr rfl
  intro S hS
  rw [← mul_sum]
  simp only [sum_boole]

/-- Pages 88 and 89, auxiliary indexed block sieve step.
The block conditions and the error bounds are supplied, not asserted to hold asymptotically. -/
lemma decompJ365_indexed_blocks_lower (I : Finset ℕ) (F : ℕ → ℕ)
    (Bs : List Block) (hG : Good Bs) (x : ℕ → ℝ)
    (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p < 1) (X : ℝ) (hX : 0 ≤ X)
    (hρ : rhoSum x Bs ≤ 1 / 10) (E : Finset ℕ → ℝ)
    (hE : ∀ S ⊆ univB Bs,
      |(#{i ∈ I | (∏ p ∈ S, p) ∣ F i} : ℝ) - X * ∏ p ∈ S, x p| ≤ E S) :
    X * (∏ p ∈ univB Bs, (1 - x p)) * (1 - 5 * rhoSum x Bs) -
      3 ^ Bs.length * ∑ S ∈ (univB Bs).powerset.filter (fun S => cL Bs S ≠ 0), E S ≤
      #{i ∈ I | ∀ p ∈ univB Bs, ¬ p ∣ F i} := by
  let R : Finset ℕ → ℝ := fun S =>
    (#{i ∈ I | (∏ p ∈ S, p) ∣ F i} : ℝ) - X * ∏ p ∈ S, x p
  have hsplit : ∑ i ∈ I, wEval (univB Bs) (cL Bs) (F i) =
      X * wMain (univB Bs) (cL Bs) x +
        ∑ S ∈ (univB Bs).powerset, cL Bs S * R S := by
    rw [decompJ365_indexed_weight_sum]
    unfold wMain
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro S hS
    dsimp [R]
    ring
  have hpoint : ∑ i ∈ I, wEval (univB Bs) (cL Bs) (F i) ≤
      (#{i ∈ I | ∀ p ∈ univB Bs, ¬ p ∣ F i} : ℝ) := by
    calc
      _ ≤ ∑ i ∈ I, xind (univB Bs) (F i) :=
        sum_le_sum (fun i _ => (blocks_pointwise Bs hG (F i)).1)
      _ = _ := by simp [xind, filter_eq_empty_iff]
  have hrem : ∑ S ∈ (univB Bs).powerset, |cL Bs S| * |R S| ≤
      3 ^ Bs.length * ∑ S ∈ (univB Bs).powerset.filter (fun S => cL Bs S ≠ 0), E S := by
    rw [mul_sum, sum_filter]
    apply sum_le_sum
    intro S hS
    split_ifs with hc
    · exact mul_le_mul (coeff_bounds Bs S).2 (hE S (mem_powerset.mp hS))
        (abs_nonneg _) (by positivity)
    · push Not at hc
      rw [hc]
      simp
  have hlo : -(∑ S ∈ (univB Bs).powerset, |cL Bs S| * |R S|) ≤
      ∑ S ∈ (univB Bs).powerset, cL Bs S * R S := by
    rw [← sum_neg_distrib]
    apply sum_le_sum
    intro S hS
    rw [← abs_mul]
    exact neg_abs_le _
  have hV : 0 ≤ ∏ p ∈ univB Bs, (1 - x p) :=
    prod_nonneg (fun p _ => sub_nonneg.mpr (hx1 p).le)
  have hd := (d_le_of_sum x hx0 (fun p => (hx1 p).le) Bs hρ).2.2.2
  have hm := (abs_le.mp (blocks_rel_dev x hx0 hx1 Bs hG).2).1
  have hmul := mul_le_mul_of_nonneg_left hd hV
  have hmain : (∏ p ∈ univB Bs, (1 - x p)) * (1 - 5 * rhoSum x Bs) ≤
      wMain (univB Bs) (cL Bs) x := by nlinarith
  have hXmain := mul_le_mul_of_nonneg_left hmain hX
  rw [hsplit] at hpoint
  nlinarith

/-- Second memoir pages 106 and 107, auxiliary level bound for all retained root errors. -/
lemma decompJ365_root_sum_le (h : ℕ) (Ω : Finset ℕ) (hΩ : ∀ p ∈ Ω, p.Prime)
    (U : Finset (Finset ℕ)) (hU : ∀ S ∈ U, S ⊆ Ω) (L : ℝ) (hL : 1 ≤ L)
    (hlevel : ∀ S ∈ U, ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L) :
    (∑ S ∈ U, (LeanLab.SchnirelmannGoldbach.S1.cnt h (∏ p ∈ S, p) : ℝ)) ≤
      L * (1 + Real.log L) ^ 2 := by
  let M := ∏ p ∈ Ω, p
  have hM : Squarefree M := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hΩ p hp) (hΩ q hq)).mpr hpq)
    · intro p hp
      exact (hΩ p hp).squarefree
  let D := U.image (fun S => ∏ p ∈ S, p)
  have hD : D ⊆ M.divisors := by
    intro d hd
    obtain ⟨S, hS, rfl⟩ := mem_image.mp hd
    apply Nat.mem_divisors.mpr
    exact ⟨Finset.prod_dvd_prod_of_subset S Ω id (hU S hS), hM.ne_zero⟩
  have hinj : Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p) U := by
    intro S hS T hT heq
    have hSp := Nat.primeFactors_prod (fun p hp => hΩ p (hU S hS hp))
    have hTp := Nat.primeFactors_prod (fun p hp => hΩ p (hU T hT hp))
    dsimp only at heq
    rw [← hSp, ← hTp, heq]
  calc
    _ = ∑ d ∈ D, (LeanLab.SchnirelmannGoldbach.S1.cnt h d : ℝ) := (sum_image hinj).symm
    _ ≤ ∑ d ∈ D, if (d : ℝ) ≤ L then (2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d else 0 := by
      apply sum_le_sum
      intro d hd
      obtain ⟨S, hS, rfl⟩ := mem_image.mp hd
      rw [ite_eq_left (hlevel S hS)]
      exact cnt_le_two_pow (hM.squarefree_of_dvd (Nat.dvd_of_mem_divisors (hD hd)))
    _ ≤ ∑ d ∈ M.divisors, if (d : ℝ) ≤ L then (2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors d else 0 :=
      sum_le_sum_of_subset_of_nonneg hD (fun d _ _ => by split_ifs <;> positivity)
    _ ≤ _ := LeanLab.PNTSieve.Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow L hL hM

/-- Page 88, auxiliary one decreasing step Brun inequality.
The first prime block sieves both factors. The second block sieves only the first factor. -/
lemma decompJ365_mixed_brun_lower (I P Q : Finset ℕ) (F G : ℕ → ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    {re ro se so : ℕ} (hre : Even re) (hro : Odd ro) (hse : Even se) (hso : Odd so) :
    (∑ i ∈ I,
      (wEval P (tc re) (F i * G i) * wEval Q (tc so) (F i) +
      wEval P (tc ro) (F i * G i) * wEval Q (tc se) (F i) -
      wEval P (tc re) (F i * G i) * wEval Q (tc se) (F i))) ≤
      (#{i ∈ I | (∀ p ∈ P, ¬ p ∣ F i * G i) ∧ ∀ p ∈ Q, ¬ p ∣ F i} : ℝ) := by
  calc
    _ ≤ ∑ i ∈ I, xind P (F i * G i) * xind Q (F i) := by
      apply sum_le_sum
      intro i hi
      obtain ⟨hl, hu⟩ := tc_bounds P hP hre hro (F i * G i)
      obtain ⟨hl', hu'⟩ := tc_bounds Q hQ hse hso (F i)
      exact two_block_pointwise_real (xind_nonneg _ _) (xind_nonneg _ _) hl hu hl' hu'
    _ = _ := by
      simp [xind, filter_eq_empty_iff, ← ite_and, and_comm]

/-- Second memoir page 106 formula 24.5, auxiliary indexed two-factor weight expansion. -/
lemma decompJ365_mixed_weight_sum (I P Q : Finset ℕ) (F G : ℕ → ℕ)
    (c d : Finset ℕ → ℝ) :
    (∑ i ∈ I, wEval P c (F i * G i) * wEval Q d (F i)) =
      ∑ S ∈ P.powerset, ∑ T ∈ Q.powerset, c S * d T *
        (#{i ∈ I | (∏ p ∈ S, p) ∣ F i * G i ∧ (∏ p ∈ T, p) ∣ F i} : ℝ) := by
  simp_rw [wEval, sum_mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro S hS
  rw [sum_comm]
  apply sum_congr rfl
  intro T hT
  have ht : ∀ i : ℕ,
      c S * ind S (F i * G i) * (d T * ind T (F i)) =
        c S * d T * (if (∏ p ∈ S, p) ∣ F i * G i ∧ (∏ p ∈ T, p) ∣ F i then 1 else 0) := by
    intro i
    unfold ind
    split_ifs <;> simp_all
  simp_rw [ht]
  rw [← mul_sum, sum_boole]

/-- Second memoir page 106 formula 24.5, auxiliary mixed cutoff remainder.
The modulus d tests both W factors and the coprime modulus e tests the first factor. -/
lemma decompJ365_mixed_W_periodic_remainder (H N d e : ℕ) (hNH : N ≤ H)
    (hd : 0 < d) (he : 0 < e) (hde : Nat.Coprime d e) :
    |(#{m ∈ range N | d ∣ m * (H - m) ∧ e ∣ m} : ℝ) -
      (LeanLab.SchnirelmannGoldbach.S1.cnt H d : ℝ) * N / (d * e)| ≤
        LeanLab.SchnirelmannGoldbach.S1.cnt H d := by
  let Q : ℕ → Prop := fun m => rootPred H d m ∧ (m : ZMod e) = 0
  have hperiod : Function.Periodic Q (d * e) := by
    intro m
    simp [Q, rootPred, Nat.cast_add, Nat.cast_mul]
  have : NeZero d := ⟨hd.ne'⟩
  have : NeZero e := ⟨he.ne'⟩
  have : NeZero (d * e) := ⟨(Nat.mul_pos hd he).ne'⟩
  let E := ZMod.chineseRemainder hde
  have hcast (m : ℕ) : E (m : ZMod (d * e)) = ((m : ZMod d), (m : ZMod e)) := by
    rw [map_natCast]
    rfl
  have hcnt : #{m ∈ range (d * e) | Q m} = LeanLab.SchnirelmannGoldbach.S1.cnt H d := by
    rw [card_zmod_roots, Fintype.card_subtype]
    refine Finset.card_bij (fun (m : ℕ) _ => (m : ZMod d)) ?_ ?_ ?_
    · intro m hm
      simp only [mem_filter, mem_range] at hm
      exact mem_filter.mpr ⟨mem_univ _, hm.2.1⟩
    · intro a ha b hb hab
      obtain ⟨haI, haQ⟩ := mem_filter.mp ha
      obtain ⟨hbI, hbQ⟩ := mem_filter.mp hb
      have heq : E (a : ZMod (d * e)) = E (b : ZMod (d * e)) := by
        rw [hcast, hcast]
        apply Prod.ext hab
        exact haQ.2.trans hbQ.2.symm
      have hz := congrArg ZMod.val (E.injective heq)
      simpa [ZMod.val_cast_of_lt (mem_range.mp haI),
        ZMod.val_cast_of_lt (mem_range.mp hbI)] using hz
    · intro z hz
      have hzroot := (mem_filter.mp hz).2
      let y := E.symm (z, 0)
      have hy : E (y.val : ZMod (d * e)) = (z, 0) := by
        rw [ZMod.natCast_zmod_val]
        exact E.apply_symm_apply _
      rw [hcast] at hy
      obtain ⟨hy1, hy2⟩ := Prod.ext_iff.mp hy
      dsimp only at hy1 hy2
      refine ⟨y.val, mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt y), ?_⟩, hy1⟩
      change rootPred H d y.val ∧ (y.val : ZMod e) = 0
      refine ⟨?_, hy2⟩
      change (y.val : ZMod d) * ((H : ZMod d) - y.val) = 0
      rw [hy1]
      exact hzroot
  have heq : #{m ∈ range N | d ∣ m * (H - m) ∧ e ∣ m} = #{m ∈ range N | Q m} := by
    congr 1
    apply filter_congr
    intro m hm
    have hmH : m ≤ H := (mem_range.mp hm).le.trans hNH
    simp only [Q, ← dvd_iff_rootPred hmH, ZMod.natCast_eq_zero_iff]
  rw [heq, ← hcnt]
  simpa only [Nat.cast_mul] using count_periodic_approx Q (Nat.mul_pos hd he) hperiod N

/-- Pages 88 and 89: survivors of the two prime cutoffs enter the exact W count. -/
lemma decompJ365_mixed_survivors_le_wCount (a b N t v : ℕ) (hv : 2 ≤ v) (_hvt : v ≤ t)
    (ht : (N : ℝ) ^ (1 / ((a : ℝ) + 1)) ≤ t)
    (hvpow : (N : ℝ) ^ (1 / ((b : ℝ) + 1)) ≤ v) :
    #{A ∈ range N | (∀ p ∈ Nat.primesLE v, ¬ p ∣ A * (N - A)) ∧
      ∀ p ∈ Nat.primesLE t \ Nat.primesLE v, ¬ p ∣ A} ≤ wCount a b N := by
  unfold wCount
  apply card_le_card
  intro A hA
  obtain ⟨hAN, hlow, hhigh⟩ := mem_filter.mp hA
  have hAN' : A < N := mem_range.mp hAN
  have hA0 : A ≠ 0 := by
    intro hzero
    apply hlow 2 (Nat.mem_primesLE.mpr ⟨hv, Nat.prime_two⟩)
    simp [hzero]
  have hA1 : 1 ≤ A := by omega
  have hB1 : 1 ≤ N - A := by omega
  have hfirst : ∀ p ∈ A.primeFactorsList, (N : ℝ) ^ (1 / ((a : ℝ) + 1)) < (p : ℝ) := by
    intro p hp
    obtain ⟨hpprime, hpdvd⟩ := (Nat.mem_primeFactorsList hA0).mp hp
    by_contra hle
    have hpt : p ≤ t := by exact_mod_cast (le_trans (not_lt.mp hle) ht)
    by_cases hpv : p ≤ v
    · exact hlow p (Nat.mem_primesLE.mpr ⟨hpv, hpprime⟩) (dvd_mul_of_dvd_left hpdvd _)
    · exact hhigh p (mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨hpt, hpprime⟩,
        fun hpv' => hpv (Nat.mem_primesLE.mp hpv').1⟩) hpdvd
  have hsecond : ∀ p ∈ (N - A).primeFactorsList,
      (N : ℝ) ^ (1 / ((b : ℝ) + 1)) < (p : ℝ) := by
    intro p hp
    obtain ⟨hpprime, hpdvd⟩ := (Nat.mem_primeFactorsList (by omega : N - A ≠ 0)).mp hp
    by_contra hle
    have hpv : p ≤ v := by exact_mod_cast (le_trans (not_lt.mp hle) hvpow)
    exact hlow p (Nat.mem_primesLE.mpr ⟨hpv, hpprime⟩) (dvd_mul_of_dvd_right hpdvd _)
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hA1, by omega⟩,
    decompJ365_almostGT_of_lt hA1 hAN' hfirst,
    decompJ365_almostGT_of_lt hB1 (by omega) hsecond⟩

/-- Pages 88 and 89, auxiliary finite block lower sieve for the Z pair polynomial.
A positive asymptotic balance of the block ratios and the level is still required. -/
lemma decompJ365_pair_blocks_lower (h N : ℕ) (Bs : List Block) (hG : Good Bs)
    (x : ℕ → ℝ) (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p < 1)
    (hx : ∀ p ∈ univB Bs, x p = nuN h p) (hρ : rhoSum x Bs ≤ 1 / 10)
    (L : ℝ) (hL : 1 ≤ L) (hlevel : (lev Bs : ℝ) ≤ L) :
    (N : ℝ) * (∏ p ∈ univB Bs, (1 - nuN h p)) * (1 - 5 * rhoSum x Bs) -
      3 ^ Bs.length * (L * (1 + Real.log L) ^ 2) ≤
      #{m ∈ range N | ∀ p ∈ univB Bs, ¬ p ∣ m * (m + h)} := by
  have hprime := univB_prime Bs hG
  have hdensity (S : Finset ℕ) (hS : S ⊆ univB Bs) :
      (LeanLab.SchnirelmannGoldbach.S1.cnt h (∏ p ∈ S, p) : ℝ) / (∏ p ∈ S, p) =
        ∏ p ∈ S, x p := by
    rw [cnt_prod_primes h S (fun p hp => hprime p (hS hp)), Nat.cast_prod, ← prod_div_distrib]
    apply prod_congr rfl
    intro p hp
    rw [hx p (hS hp), nuN_prime (hprime p (hS hp))]
  have hE (S : Finset ℕ) (hS : S ⊆ univB Bs) :
      |(#{m ∈ range N | (∏ p ∈ S, p) ∣ m * (m + h)} : ℝ) -
        N * ∏ p ∈ S, x p| ≤ LeanLab.SchnirelmannGoldbach.S1.cnt h (∏ p ∈ S, p) := by
    have hd : 0 < ∏ p ∈ S, p := prod_pos (fun p hp => (hprime p (hS hp)).pos)
    have heq : (N : ℝ) * ∏ p ∈ S, x p =
        (LeanLab.SchnirelmannGoldbach.S1.cnt h (∏ p ∈ S, p) : ℝ) * N / (∏ p ∈ S, p) := by
      rw [← hdensity S hS]
      ring
    rw [heq]
    exact decompJ365_pair_periodic_remainder h N _ hd
  have hraw := decompJ365_indexed_blocks_lower (range N) (fun m => m * (m + h))
    Bs hG x hx0 hx1 N (Nat.cast_nonneg N) hρ
    (fun S => (LeanLab.SchnirelmannGoldbach.S1.cnt h (∏ p ∈ S, p) : ℝ)) hE
  have hrem := decompJ365_root_sum_le h (univB Bs) hprime
    ((univB Bs).powerset.filter (fun S => cL Bs S ≠ 0))
    (fun S hS => mem_powerset.mp (mem_filter.mp hS).1) L hL (by
      intro S hS
      have hS' := mem_filter.mp hS
      have hsupp := support_prod Bs hG S (mem_powerset.mp hS'.1) (Or.inl hS'.2)
      exact (by exact_mod_cast hsupp : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ lev Bs).trans hlevel)
  have hprod : (∏ p ∈ univB Bs, (1 - x p)) = ∏ p ∈ univB Bs, (1 - nuN h p) :=
    prod_congr rfl (fun p hp => by rw [hx p hp])
  rw [hprod] at hraw
  have hmul := mul_le_mul_of_nonneg_left hrem (by positivity : (0 : ℝ) ≤ 3 ^ Bs.length)
  linarith

/-- Pages 88 and 89, auxiliary finite block lower sieve for the W pair polynomial.
A positive asymptotic balance of the block ratios and the level is still required. -/
lemma decompJ365_W_blocks_lower (N : ℕ) (Bs : List Block) (hG : Good Bs)
    (x : ℕ → ℝ) (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p < 1)
    (hx : ∀ p ∈ univB Bs, x p = nuN N p) (hρ : rhoSum x Bs ≤ 1 / 10)
    (L : ℝ) (hL : 1 ≤ L) (hlevel : (lev Bs : ℝ) ≤ L) :
    (N : ℝ) * (∏ p ∈ univB Bs, (1 - nuN N p)) * (1 - 5 * rhoSum x Bs) -
      3 ^ Bs.length * (L * (1 + Real.log L) ^ 2) ≤
      #{m ∈ range N | ∀ p ∈ univB Bs, ¬ p ∣ m * (N - m)} := by
  have hprime := univB_prime Bs hG
  have hE (S : Finset ℕ) (hS : S ⊆ univB Bs) :
      |(#{m ∈ range N | (∏ p ∈ S, p) ∣ m * (N - m)} : ℝ) -
        N * ∏ p ∈ S, x p| ≤ LeanLab.SchnirelmannGoldbach.S1.cnt N (∏ p ∈ S, p) := by
    have hc := LeanLab.SchnirelmannGoldbach.PureSieve.multiples_error N S
      (fun p hp => hprime p (hS hp))
    have hxS : (∏ p ∈ S, (LeanLab.SchnirelmannGoldbach.S1.wt N p / p)) = ∏ p ∈ S, x p := by
      apply prod_congr rfl
      intro p hp
      rw [hx p (hS hp), nuN_prime (hprime p (hS hp))]
    rw [hxS] at hc
    rw [cnt_prod_primes N S (fun p hp => hprime p (hS hp))]
    simpa only [LeanLab.SchnirelmannGoldbach.PureSieve.multiples] using hc
  have hraw := decompJ365_indexed_blocks_lower (range N) (fun m => m * (N - m))
    Bs hG x hx0 hx1 N (Nat.cast_nonneg N) hρ
    (fun S => (LeanLab.SchnirelmannGoldbach.S1.cnt N (∏ p ∈ S, p) : ℝ)) hE
  have hrem := decompJ365_root_sum_le N (univB Bs) hprime
    ((univB Bs).powerset.filter (fun S => cL Bs S ≠ 0))
    (fun S hS => mem_powerset.mp (mem_filter.mp hS).1) L hL (by
      intro S hS
      have hS' := mem_filter.mp hS
      have hsupp := support_prod Bs hG S (mem_powerset.mp hS'.1) (Or.inl hS'.2)
      exact (by exact_mod_cast hsupp : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ lev Bs).trans hlevel)
  have hprod : (∏ p ∈ univB Bs, (1 - x p)) = ∏ p ∈ univB Bs, (1 - nuN N p) :=
    prod_congr rfl (fun p hp => by rw [hx p hp])
  rw [hprod] at hraw
  have hmul := mul_le_mul_of_nonneg_left hrem (by positivity : (0 : ℝ) ≤ 3 ^ Bs.length)
  linarith

/-- Negative auxiliary route check for page 88: at every fixed pure Brun order,
the factorial error majorant eventually exceeds the entire density product. -/
lemma decompJ365_fixed_brun_certificate_negative (h r : ℕ) (heven : Even h) :
    ∀ᶠ z : ℕ in atTop,
      (∏ p ∈ Nat.primesLE z, (1 - nuN h p)) -
        (∑ p ∈ Nat.primesLE z, nuN h p) ^ (r + 1) / ((r + 1).factorial : ℝ) < 0 := by
  let f : ℕ → ℝ := Set.indicator {p | p.Prime} (fun p => (1 : ℝ) / p)
  have hf0 : ∀ p, 0 ≤ f p := fun p => Set.indicator_nonneg (fun q _ => by positivity) p
  have hdiv : Tendsto (fun z : ℕ => ∑ p ∈ range z, f p) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hf0).mp not_summable_one_div_on_primes
  have hmass : ∀ z : ℕ, (∑ p ∈ range z, f p) ≤ ∑ p ∈ Nat.primesLE z, nuN h p := by
    intro z
    have hsub : (range z).filter Nat.Prime ⊆ Nat.primesLE z := by
      intro p hp
      obtain ⟨hpz, hpprime⟩ := mem_filter.mp hp
      exact Nat.mem_primesLE.mpr ⟨(mem_range.mp hpz).le, hpprime⟩
    have hsum : (∑ p ∈ range z, f p) = ∑ p ∈ (range z).filter Nat.Prime, (1 : ℝ) / p := by
      rw [sum_filter]
      apply sum_congr rfl
      intro p hp
      by_cases hpp : p.Prime <;> simp [f, hpp]
    rw [hsum]
    calc
      _ ≤ ∑ p ∈ (range z).filter Nat.Prime, nuN h p := by
        apply sum_le_sum
        intro p hp
        rw [nuN_prime (mem_filter.mp hp).2]
        exact div_le_div_of_nonneg_right (one_le_wt h p) (Nat.cast_nonneg p)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => nuN_nonneg h p)
  have hmassdiv : Tendsto (fun z : ℕ => ∑ p ∈ Nat.primesLE z, nuN h p) atTop atTop :=
    tendsto_atTop_mono hmass hdiv
  filter_upwards [hmassdiv.eventually (eventually_ge_atTop (((r + 1).factorial : ℝ) + 2))] with z hz
  have hfac : (0 : ℝ) < (r + 1).factorial := by exact_mod_cast Nat.factorial_pos (r + 1)
  have hmass1 : 1 ≤ ∑ p ∈ Nat.primesLE z, nuN h p := by linarith
  have hp := le_self_pow₀ hmass1 (by omega : r + 1 ≠ 0)
  have herr : 1 < (∑ p ∈ Nat.primesLE z, nuN h p) ^ (r + 1) / ((r + 1).factorial : ℝ) := by
    apply (one_lt_div hfac).mpr
    linarith
  have hprod : (∏ p ∈ Nat.primesLE z, (1 - nuN h p)) ≤ 1 := by
    apply prod_le_one₀
    · intro p hp
      exact sub_nonneg.mpr (nuN_lt_one heven (Nat.prime_of_mem_primesLE hp)).le
    · intro p hp
      exact sub_le_self _ (nuN_nonneg h p)
  linarith

/-- Pages 75, 88 and 89: fixed roughness cutoffs and strict size margins
supply the factor counts for either sign of the Z shift. -/
lemma decompJ365_rough_survivors_le_zCount (a b ξ : ℕ) (m : ℤ) (R S : ℝ)
    (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hsizeR : (ξ : ℝ) < R ^ (a + 1))
    (hsizeS : ((ξ + 2 * m.natAbs : ℕ) : ℝ) < S ^ (b + 1))
    (htR : (ξ : ℝ) ^ (1 / ((a : ℝ) + 1)) ≤ R)
    (htS : (ξ : ℝ) ^ (1 / ((b : ℝ) + 1)) ≤ S) :
    #{x ∈ Icc (1 : ℕ) ξ | 0 < ((x : ℕ) : ℤ) + 2 * m ∧
      (∀ p : ℕ, p.Prime → p ∣ x → R < (p : ℝ)) ∧
      ∀ p : ℕ, p.Prime → p ∣ (((x : ℕ) : ℤ) + 2 * m).toNat → S < (p : ℝ)} ≤ zCount a b m ξ := by
  unfold zCount
  apply card_le_card
  intro x hx
  rw [mem_filter] at hx
  obtain ⟨hxI, hpos, hfirst, hsecond⟩ := hx
  obtain ⟨hx1, hxξ⟩ := mem_Icc.mp hxI
  have hBcast : ((((x : ℕ) : ℤ) + 2 * m).toNat : ℤ) = ((x : ℕ) : ℤ) + 2 * m :=
    Int.toNat_of_nonneg hpos.le
  have hmabs : m ≤ (m.natAbs : ℤ) := Int.le_natAbs
  have hB1 : 1 ≤ (((x : ℕ) : ℤ) + 2 * m).toNat := by omega
  have hBbound : (((x : ℕ) : ℤ) + 2 * m).toNat ≤ ξ + 2 * m.natAbs := by omega
  have hroughA : ∀ p ∈ x.primeFactorsList, R < (p : ℝ) := by
    intro p hp
    obtain ⟨hpprime, hpdvd⟩ := (Nat.mem_primeFactorsList (by omega : x ≠ 0)).mp hp
    exact hfirst p hpprime hpdvd
  have hroughB : ∀ p ∈ ((((x : ℕ) : ℤ) + 2 * m).toNat).primeFactorsList, S < (p : ℝ) := by
    intro p hp
    obtain ⟨hpprime, hpdvd⟩ := (Nat.mem_primeFactorsList (by omega : (((x : ℕ) : ℤ) + 2 * m).toNat ≠ 0)).mp hp
    exact hsecond p hpprime hpdvd
  have hfirst' := almostGT_of_pow_bound hx1 hR hroughA
    ((by exact_mod_cast hxξ : (x : ℝ) ≤ ξ).trans_lt hsizeR)
  have hBboundR : (((((x : ℕ) : ℤ) + 2 * m).toNat) : ℝ) ≤ ((ξ + 2 * m.natAbs : ℕ) : ℝ) := by
    exact_mod_cast hBbound
  have hsecond' := almostGT_of_pow_bound hB1 hS hroughB (hBboundR.trans_lt hsizeS)
  have hxcast : (x : ℝ) ≤ ξ := by exact_mod_cast hxξ
  refine mem_filter.mpr ⟨hxI, almostGT_mono hfirst' le_rfl ?_, hpos,
    almostGT_mono hsecond' le_rfl ?_⟩
  · exact (Real.rpow_le_rpow (Nat.cast_nonneg x) hxcast (by positivity)).trans htR
  · exact (Real.rpow_le_rpow (Nat.cast_nonneg x) hxcast (by positivity)).trans htS

/-- Second memoir pages 106 and 107, auxiliary discrepancy bound for mixed indexed weights. -/
lemma decompJ365_mixed_weight_error (I P Q : Finset ℕ) (F G : ℕ → ℕ)
    (c d : Finset ℕ → ℝ) (x y : ℕ → ℝ) (X : ℝ)
    (E : Finset ℕ → Finset ℕ → ℝ)
    (hE : ∀ S ⊆ P, ∀ T ⊆ Q,
      |(#{i ∈ I | (∏ p ∈ S, p) ∣ F i * G i ∧ (∏ p ∈ T, p) ∣ F i} : ℝ) -
        X * (∏ p ∈ S, x p) * (∏ p ∈ T, y p)| ≤ E S T) :
    |(∑ i ∈ I, wEval P c (F i * G i) * wEval Q d (F i)) -
      X * wMain P c x * wMain Q d y| ≤
      ∑ S ∈ P.powerset, ∑ T ∈ Q.powerset, |c S| * |d T| * E S T := by
  have hsplit : (∑ i ∈ I, wEval P c (F i * G i) * wEval Q d (F i)) -
      X * wMain P c x * wMain Q d y =
      ∑ S ∈ P.powerset, ∑ T ∈ Q.powerset, c S * d T *
        ((#{i ∈ I | (∏ p ∈ S, p) ∣ F i * G i ∧ (∏ p ∈ T, p) ∣ F i} : ℝ) -
          X * (∏ p ∈ S, x p) * (∏ p ∈ T, y p)) := by
    rw [decompJ365_mixed_weight_sum]
    unfold wMain
    rw [mul_assoc X, sum_mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro S hS
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro T hT
    ring
  rw [hsplit]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro S hS
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro T hT
  rw [abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hE S (mem_powerset.mp hS) T (mem_powerset.mp hT))
    (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- Pages 88 and 89 and second memoir page 106: explicit mixed W weight discrepancy. -/
lemma decompJ365_mixed_W_weight_error (N : ℕ) (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime) (hPQ : Disjoint P Q)
    (c d : Finset ℕ → ℝ) :
    |(∑ m ∈ range N, wEval P c (m * (N - m)) * wEval Q d m) -
      N * wMain P c (fun p => nuN N p) * wMain Q d (fun p => (1 : ℝ) / p)| ≤
      (∑ S ∈ P.powerset, |c S| * (LeanLab.SchnirelmannGoldbach.S1.cnt N (∏ p ∈ S, p) : ℝ)) *
        (∑ T ∈ Q.powerset, |d T|) := by
  have hE (S : Finset ℕ) (hS : S ⊆ P) (T : Finset ℕ) (hT : T ⊆ Q) :
      |(#{m ∈ range N | (∏ p ∈ S, p) ∣ m * (N - m) ∧ (∏ p ∈ T, p) ∣ m} : ℝ) -
        N * (∏ p ∈ S, nuN N p) * (∏ p ∈ T, (1 : ℝ) / p)| ≤
          LeanLab.SchnirelmannGoldbach.S1.cnt N (∏ p ∈ S, p) := by
    have hd : 0 < ∏ p ∈ S, p := prod_pos (fun p hp => (hP p (hS hp)).pos)
    have he : 0 < ∏ p ∈ T, p := prod_pos (fun p hp => (hQ p (hT hp)).pos)
    have hcop := coprime_prod_of_disjoint hP hQ hPQ hS hT
    have hl : (LeanLab.SchnirelmannGoldbach.S1.cnt N (∏ p ∈ S, p) : ℝ) / (∏ p ∈ S, p) =
        ∏ p ∈ S, nuN N p := by
      rw [cnt_prod_primes N S (fun p hp => hP p (hS hp)), Nat.cast_prod, ← prod_div_distrib]
      apply prod_congr rfl
      intro p hp
      rw [nuN_prime (hP p (hS hp))]
    have hh : (∏ p ∈ T, (1 : ℝ) / p) = 1 / ((∏ p ∈ T, p : ℕ) : ℝ) := by
      rw [prod_div_distrib, prod_const_one, Nat.cast_prod]
    have hmain : (N : ℝ) * (∏ p ∈ S, nuN N p) * (∏ p ∈ T, (1 : ℝ) / p) =
        (LeanLab.SchnirelmannGoldbach.S1.cnt N (∏ p ∈ S, p) : ℝ) * N /
          ((∏ p ∈ S, p : ℕ) * (∏ p ∈ T, p : ℕ)) := by
      rw [← hl, hh]
      field_simp
    rw [hmain]
    exact decompJ365_mixed_W_periodic_remainder N N _ _ le_rfl hd he hcop
  have hraw := decompJ365_mixed_weight_error (range N) P Q (fun m => m) (fun m => N - m)
    c d (fun p => nuN N p) (fun p => (1 : ℝ) / p) N
    (fun S _ => (LeanLab.SchnirelmannGoldbach.S1.cnt N (∏ p ∈ S, p) : ℝ)) hE
  refine hraw.trans_eq ?_
  rw [sum_mul_sum]
  apply sum_congr rfl
  intro S hS
  apply sum_congr rfl
  intro T hT
  ring

/-- Negative auxiliary route check for page 88: an odd level one block with
reciprocal density mass at least one half fails the relative error budget one tenth. -/
lemma decompJ365_shallow_block_ratio_gt (P : Finset ℕ) (x : ℕ → ℝ)
    (hx0 : ∀ p, 0 ≤ x p) (hx1 : ∀ p, x p < 1)
    (hmass : (1 / 2 : ℝ) ≤ ∑ p ∈ P, x p) (re : ℕ) :
    (1 / 10 : ℝ) < rho x (P, re, 1) := by
  let V := ∏ p ∈ P, (1 - x p)
  have hV : 0 < V := prod_pos (fun p _ => sub_pos.mpr (hx1 p))
  have hV1 : V ≤ 1 := prod_le_one₀ (fun p _ => sub_nonneg.mpr (hx1 p).le)
    (fun p _ => sub_le_self _ (hx0 p))
  have hr0 := rho_nonneg x hx0 (fun p => (hx1 p).le) (P, re, 1)
  have hE : truncErr P x 1 ≤ rho x (P, re, 1) * V := by
    dsimp [rho, V]
    rw [div_mul_cancel₀ _ hV.ne']
    exact le_max_right _ _
  have hE0 : (1 / 8 : ℝ) ≤ truncErr P x 1 := by
    norm_num [truncErr]
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hV1 hr0
  nlinarith

/-- Second memoir pages 92 and 93 formula 11.5, auxiliary Brun pairing step.
Erasing a distinguished element preserves admissibility. Every admissible even
subset avoiding that element has an admissible extension. -/
lemma decompJ365_brun_toggle_lower (γ : Finset ℕ) (ν : ℕ) (hν : ν ∈ γ)
    (A : Finset ℕ → Prop) [DecidablePred A]
    (herase : ∀ S ⊆ γ, A S → A (S.erase ν))
    (hext : ∀ S ⊆ γ, ν ∉ S → Even S.card → A S → A (insert ν S)) :
    (∑ S ∈ γ.powerset, if A S then (-1 : ℝ) ^ S.card else 0) ≤ 0 := by
  have hνnot : ν ∉ γ.erase ν := notMem_erase ν γ
  have hγ : insert ν (γ.erase ν) = γ := insert_erase hν
  rw [← hγ, sum_powerset_insert hνnot, ← sum_add_distrib]
  apply sum_nonpos
  intro S hS
  have hSsub : S ⊆ γ := (mem_powerset.mp hS).trans (erase_subset ν γ)
  have hνS : ν ∉ S := notMem_of_mem_powerset_of_notMem hS hνnot
  have hinsub : insert ν S ⊆ γ := insert_subset hν hSsub
  have herase' : A (insert ν S) → A S := by
    intro hi
    simpa only [erase_insert hνS] using herase (insert ν S) hinsub hi
  rw [card_insert_of_notMem hνS, pow_succ]
  by_cases hAS : A S
  · rw [ite_eq_left hAS]
    rcases Nat.even_or_odd S.card with heven | hodd
    · rw [ite_eq_left (hext S hSsub hνS heven hAS), heven.neg_one_pow]
      norm_num
    · rw [hodd.neg_one_pow]
      split_ifs <;> norm_num
  · rw [ite_eq_right hAS, ite_eq_right (fun hi => hAS (herase' hi))]
    norm_num

/-- Second memoir pages 92, 93 and 107, auxiliary indexed Brun lower sieve.
The supplied admissible family satisfies the erase and even extension pairing conditions. -/
lemma decompJ365_decreasing_family_lower (I P : Finset ℕ) (F : ℕ → ℕ)
    (hP : ∀ p ∈ P, p.Prime) (A : Finset ℕ → Prop) [DecidablePred A] (hA0 : A ∅)
    (hpair : ∀ γ ⊆ P, γ.Nonempty → ∃ ν ∈ γ,
      (∀ S ⊆ γ, A S → A (S.erase ν)) ∧
      ∀ S ⊆ γ, ν ∉ S → Even S.card → A S → A (insert ν S)) :
    (∑ S ∈ P.powerset, (if A S then (-1 : ℝ) ^ S.card else 0) *
      (#{i ∈ I | (∏ p ∈ S, p) ∣ F i} : ℝ)) ≤
      #{i ∈ I | ∀ p ∈ P, ¬ p ∣ F i} := by
  have hpoint (n : ℕ) : wEval P (fun S => if A S then (-1 : ℝ) ^ S.card else 0) n ≤ xind P n := by
    let γ := P.filter (· ∣ n)
    have hγP : γ ⊆ P := filter_subset _ _
    have hsets : P.powerset.filter (fun S => (∏ p ∈ S, p) ∣ n) = γ.powerset := by
      ext S
      simp only [mem_filter, mem_powerset]
      constructor
      · rintro ⟨hSP, hd⟩
        exact (dvd_iff_subset P hP hSP n).mp hd
      · intro hSγ
        have hSP := hSγ.trans hγP
        exact ⟨hSP, (dvd_iff_subset P hP hSP n).mpr hSγ⟩
    have hsum : wEval P (fun S => if A S then (-1 : ℝ) ^ S.card else 0) n =
        ∑ S ∈ γ.powerset, if A S then (-1 : ℝ) ^ S.card else 0 := by
      unfold wEval ind
      simp only [mul_ite, mul_one, mul_zero]
      rw [← sum_filter, hsets]
    rw [hsum]
    by_cases hγ : γ = ∅
    · simp [hγ, xind, hA0, show P.filter (· ∣ n) = ∅ from hγ]
    · obtain ⟨ν, hν, herase, hext⟩ := hpair γ hγP (nonempty_iff_ne_empty.mpr hγ)
      have hz : xind P n = 0 := ite_eq_right hγ
      rw [hz]
      exact decompJ365_brun_toggle_lower γ ν hν A herase hext
  rw [← decompJ365_indexed_weight_sum]
  calc
    _ ≤ ∑ i ∈ I, xind P (F i) := sum_le_sum (fun i _ => hpoint (F i))
    _ = _ := by simp [xind, filter_eq_empty_iff]

/-- Second memoir pages 91 to 93 and 107, auxiliary decreasing step Brun sieve.
Each nested upper prime segment has an odd cardinality cap on retained subsets. -/
lemma decompJ365_decreasing_brun_lower (I P J : Finset ℕ) (F : ℕ → ℕ)
    (hP : ∀ p ∈ P, p.Prime) (cutoff level : ℕ → ℕ) :
    (∑ S ∈ P.powerset.filter (fun S => ∀ j ∈ J,
        (S.filter (fun p => cutoff j < p)).card ≤ 2 * level j + 1),
      (-1 : ℝ) ^ S.card * (#{i ∈ I | (∏ p ∈ S, p) ∣ F i} : ℝ)) ≤
      #{i ∈ I | ∀ p ∈ P, ¬ p ∣ F i} := by
  let A : Finset ℕ → Prop := fun S => ∀ j ∈ J,
    (S.filter (fun p => cutoff j < p)).card ≤ 2 * level j + 1
  have hA0 : A ∅ := by simp [A]
  have hpair : ∀ γ ⊆ P, γ.Nonempty → ∃ ν ∈ γ,
      (∀ S ⊆ γ, A S → A (S.erase ν)) ∧
      ∀ S ⊆ γ, ν ∉ S → Even S.card → A S → A (insert ν S) := by
    intro γ hγP hγ
    let ν := γ.min' hγ
    have hν : ν ∈ γ := min'_mem γ hγ
    refine ⟨ν, hν, ?_, ?_⟩
    · intro S hS hAS j hj
      have hsub : (S.erase ν).filter (fun p => cutoff j < p) ⊆
          S.filter (fun p => cutoff j < p) := by
        intro p hp
        obtain ⟨hpS, hpc⟩ := mem_filter.mp hp
        exact mem_filter.mpr ⟨(mem_erase.mp hpS).2, hpc⟩
      exact (card_le_card hsub).trans (hAS j hj)
    · intro S hS hνS hEven hAS j hj
      by_cases hcν : cutoff j < ν
      · have hall : ∀ p ∈ S, cutoff j < p := fun p hp =>
          hcν.trans_le (min'_le γ p (hS hp))
        have hf : S.filter (fun p => cutoff j < p) = S := filter_eq_self.mpr hall
        have hfi : (insert ν S).filter (fun p => cutoff j < p) = insert ν S := by
          apply filter_eq_self.mpr
          intro p hp
          rcases mem_insert.mp hp with rfl | hp
          · exact hcν
          · exact hall p hp
        have hbound := hAS j hj
        rw [hf] at hbound
        rw [hfi, card_insert_of_notMem hνS]
        rcases hEven with ⟨k, hk⟩
        omega
      · simpa only [filter_insert, ite_eq_right hcν] using hAS j hj
  have hlower := decompJ365_decreasing_family_lower I P F hP A hA0 hpair
  rw [sum_filter]
  simpa only [A, ite_mul, zero_mul] using hlower

/-- First memoir page 81 formula 2.6: the three block lower head is exactly
the signed factorial sum with nested odd caps one, three and five. -/
lemma decompJ365_lower_head_identity (t₁ t₂ t₃ : ℚ) :
    (∑ i ∈ range 2, ∑ j ∈ range 4, ∑ k ∈ range 6,
      if i + j ≤ 3 ∧ i + j + k ≤ 5 then
        (-1 : ℚ) ^ (i + j + k) * (t₁ ^ i / (i.factorial : ℚ)) *
          (t₂ ^ j / (j.factorial : ℚ)) * (t₃ ^ k / (k.factorial : ℚ)) else 0) =
      Ebar3 t₁ t₂ t₃ := by
  norm_num [sum_range_succ, Nat.factorial, Ebar3]
  ring

/-- Second memoir page 107, auxiliary support gain from one decreasing step.
One large element costs t and the remaining at most 2r elements cost v each. -/
lemma decompJ365_one_step_support (S : Finset ℕ) (t v r : ℕ) (hv : 1 ≤ v) (hvt : v ≤ t)
    (ht : ∀ p ∈ S, p ≤ t) (hcard : S.card ≤ 2 * r + 1)
    (hhigh : (S.filter (fun p => v < p)).card ≤ 1) :
    (∏ p ∈ S, p) ≤ t * v ^ (2 * r) := by
  by_cases hall : ∀ p ∈ S, p ≤ v
  · calc
      _ ≤ v ^ S.card := prod_le_pow_card S id v hall
      _ ≤ v ^ (2 * r + 1) := Nat.pow_le_pow_right hv hcard
      _ = v * v ^ (2 * r) := pow_succ' _ _
      _ ≤ _ := Nat.mul_le_mul_right _ hvt
  · push Not at hall
    obtain ⟨q, hq, hqv⟩ := hall
    have hqh : q ∈ S.filter (fun p => v < p) := mem_filter.mpr ⟨hq, hqv⟩
    have hsmall : ∀ p ∈ S.erase q, p ≤ v := by
      intro p hp
      obtain ⟨hpq, hpS⟩ := mem_erase.mp hp
      by_contra hpv
      have hph : p ∈ S.filter (fun p => v < p) := mem_filter.mpr ⟨hpS, lt_of_not_ge hpv⟩
      exact hpq (card_le_one.mp hhigh p hph q hqh)
    have hcard' : (S.erase q).card ≤ 2 * r := by
      rw [card_erase_of_mem hq]
      omega
    rw [← mul_prod_erase S (fun p : ℕ => p) hq]
    exact Nat.mul_le_mul (ht q hq)
      ((prod_le_pow_card (S.erase q) id v hsmall).trans (Nat.pow_le_pow_right hv hcard'))

/-- Second memoir pages 106 and 107, auxiliary decreasing step lower sieve with
an explicit level remainder. The retained main sum still needs an analytic lower bound. -/
lemma decompJ365_decreasing_lower_explicit (I P J : Finset ℕ) (F : ℕ → ℕ)
    (hP : ∀ p ∈ P, p.Prime) (cutoff level : ℕ → ℕ) (h : ℕ) (X : ℝ) (x : ℕ → ℝ)
    (herror : ∀ S ⊆ P,
      |(#{i ∈ I | (∏ p ∈ S, p) ∣ F i} : ℝ) - X * ∏ p ∈ S, x p| ≤
        LeanLab.SchnirelmannGoldbach.S1.cnt h (∏ p ∈ S, p))
    (L : ℝ) (hL : 1 ≤ L)
    (hlevel : ∀ S ⊆ P, (∀ j ∈ J,
      (S.filter (fun p => cutoff j < p)).card ≤ 2 * level j + 1) →
        ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L) :
    let U := P.powerset.filter (fun S => ∀ j ∈ J,
      (S.filter (fun p => cutoff j < p)).card ≤ 2 * level j + 1)
    X * (∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, x p) - L * (1 + Real.log L) ^ 2 ≤
      #{i ∈ I | ∀ p ∈ P, ¬ p ∣ F i} := by
  let U := P.powerset.filter (fun S => ∀ j ∈ J,
    (S.filter (fun p => cutoff j < p)).card ≤ 2 * level j + 1)
  have hUP : ∀ S ∈ U, S ⊆ P := fun S hS => mem_powerset.mp (mem_filter.mp hS).1
  have hterm (S : Finset ℕ) (hS : S ∈ U) :
      X * ((-1 : ℝ) ^ S.card * ∏ p ∈ S, x p) -
        LeanLab.SchnirelmannGoldbach.S1.cnt h (∏ p ∈ S, p) ≤
      (-1 : ℝ) ^ S.card * (#{i ∈ I | (∏ p ∈ S, p) ∣ F i} : ℝ) := by
    have herr : |(-1 : ℝ) ^ S.card *
        ((#{i ∈ I | (∏ p ∈ S, p) ∣ F i} : ℝ) - X * ∏ p ∈ S, x p)| ≤
          LeanLab.SchnirelmannGoldbach.S1.cnt h (∏ p ∈ S, p) := by
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using herror S (hUP S hS)
    have hlo := (abs_le.mp herr).1
    nlinarith
  have hsum := sum_le_sum hterm
  rw [sum_sub_distrib, ← mul_sum] at hsum
  have hraw := decompJ365_decreasing_brun_lower I P J F hP cutoff level
  have hrem := decompJ365_root_sum_le h P hP U hUP L hL
    (fun S hS => hlevel S (hUP S hS) (mem_filter.mp hS).2)
  change X * (∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, x p) - L * (1 + Real.log L) ^ 2 ≤ _
  change (∑ S ∈ U, (-1 : ℝ) ^ S.card *
    (#{i ∈ I | (∏ p ∈ S, p) ∣ F i} : ℝ)) ≤ _ at hraw
  linarith

/-- Second memoir pages 108 and 109, auxiliary sharp reciprocal prime block upper bound.
Partial summation of the lab Mertens bounds gives a vanishing endpoint loss. -/
lemma decompJ365_prime_block_upper (y w : ℕ) (hy : 2 ≤ y) (hyw : y ≤ w) :
    (∑ p ∈ (Ioc y w).filter Nat.Prime, (1 : ℝ) / p) ≤
      Real.log (Real.log w / Real.log y) + 14 / Real.log y := by
  have hyR : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hwR : (2 : ℝ) ≤ w := by exact_mod_cast hy.trans hyw
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hlw : 0 < Real.log w := Real.log_pos (by linarith)
  have hsplitE : E w = E y + ∑ p ∈ (Ioc y w).filter Nat.Prime, (1 : ℝ) / p := by
    rw [E_eq, E_eq]
    have hsets : (Icc 1 w).filter Nat.Prime =
        (Icc 1 y).filter Nat.Prime ∪ (Ioc y w).filter Nat.Prime := by
      rw [← filter_union]
      congr 1
      ext p
      simp only [mem_union, mem_Icc, mem_Ioc]
      omega
    rw [hsets, sum_union]
    rw [disjoint_left]
    intro p hp hq
    have hp' := (mem_Icc.mp (mem_filter.mp hp).1).2
    have hq' := (mem_Ioc.mp (mem_filter.mp hq).1).1
    omega
  have hab : E w - E y = C w / Real.log w - C y / Real.log y +
      ∑ n ∈ Ico y w, C n * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) := by
    have hw := abel w (hy.trans hyw)
    have hy' := abel y hy
    have hs := sum_Ico_consecutive
      (fun n : ℕ => C n * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1))) hy hyw
    linarith
  have hb1 : C w / Real.log w ≤ 1 + 7 / Real.log w := by
    rw [div_le_iff₀ hlw, add_mul, one_mul, div_mul_cancel₀ _ hlw.ne']
    exact C_le w (by omega)
  have hb2 : 1 - 7 / Real.log y ≤ C y / Real.log y := by
    apply (le_div_iff₀ hly).mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hly.ne']
    exact C_ge y
  have hterm : ∀ n ∈ Ico y w, C n * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) ≤
      (Real.log (Real.log ((n : ℝ) + 1)) - Real.log (Real.log n)) +
        7 * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) := by
    intro n hn
    have hn2 : 2 ≤ n := hy.trans (mem_Ico.mp hn).1
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hl : 0 < Real.log n := Real.log_pos (by linarith)
    have hl1 : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by linarith)
    have hd := diff_nonneg hn2
    have h1 := mul_le_mul_of_nonneg_right (C_le n (by omega)) hd
    have h2 : Real.log n * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) ≤
        Real.log (Real.log ((n : ℝ) + 1)) - Real.log (Real.log n) := by
      rw [← Real.log_div hl1.ne' hl.ne']
      have hh := Real.one_sub_inv_le_log_of_pos (div_pos hl1 hl)
      rw [inv_div] at hh
      have heq : Real.log n * (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) =
          1 - Real.log n / Real.log ((n : ℝ) + 1) := by field_simp
      rw [heq]
      exact hh
    nlinarith
  have hs := sum_le_sum hterm
  rw [sum_add_distrib, ← mul_sum] at hs
  have htele (g : ℕ → ℝ) : ∑ n ∈ Ico y w, (g (n + 1) - g n) = g w - g y := by
    have hw := tele_sum w (hy.trans hyw) g
    have hy' := tele_sum y hy g
    have hh := sum_Ico_consecutive (fun n => g (n + 1) - g n) hy hyw
    linarith
  have ht1 : ∑ n ∈ Ico y w, (Real.log (Real.log ((n : ℝ) + 1)) - Real.log (Real.log n)) =
      Real.log (Real.log w) - Real.log (Real.log y) := by
    simpa only [Nat.cast_add, Nat.cast_one] using htele (fun n => Real.log (Real.log n))
  have ht2 : ∑ n ∈ Ico y w, (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1)) =
      1 / Real.log y - 1 / Real.log w := by
    have hh := htele (fun n => -(1 / Real.log n))
    simp only [Nat.cast_add, Nat.cast_one, sub_neg_eq_add] at hh
    have heq : (∑ n ∈ Ico y w, (1 / Real.log n - 1 / Real.log ((n : ℝ) + 1))) =
        ∑ n ∈ Ico y w, (-(1 / Real.log ((n : ℝ) + 1)) + 1 / Real.log n) :=
      sum_congr rfl (fun n _ => by ring)
    rw [heq, hh]
    ring
  rw [ht1, ht2] at hs
  rw [Real.log_div hlw.ne' hly.ne']
  have he1 : 7 / Real.log w = 7 * (1 / Real.log w) := by ring
  have he2 : 7 / Real.log y = 7 * (1 / Real.log y) := by ring
  have he3 : 14 / Real.log y = 14 * (1 / Real.log y) := by ring
  linarith

/-- First memoir page 88 and second memoir page 109: the pair root density
mass on a prime block has the dimension two logarithmic upper bound. -/
lemma decompJ365_pair_block_mass_upper (h y w : ℕ) (hy : 2 ≤ y) (hyw : y ≤ w) :
    (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p) ≤
      2 * Real.log (Real.log w / Real.log y) + 28 / Real.log y := by
  calc
    _ ≤ ∑ p ∈ (Ioc y w).filter Nat.Prime, 2 * ((1 : ℝ) / p) := by
      apply sum_le_sum
      intro p hp
      rw [nuN_prime (mem_filter.mp hp).2]
      simpa only [mul_one_div] using
        div_le_div_of_nonneg_right (wt_le_two h p) (Nat.cast_nonneg p)
    _ = 2 * ∑ p ∈ (Ioc y w).filter Nat.Prime, (1 : ℝ) / p := (mul_sum _ _ _).symm
    _ ≤ 2 * (Real.log (Real.log w / Real.log y) + 14 / Real.log y) :=
      mul_le_mul_of_nonneg_left (decompJ365_prime_block_upper y w hy hyw) (by norm_num)
    _ = _ := by ring

/-- Second memoir page 109: each fixed logarithmic prime block has an eventual
uniform dimension two mass budget, with any positive endpoint allowance. -/
lemma decompJ365_pair_block_mass_eventually (θ ε : ℝ) (hε : 0 < ε) :
    ∃ Y : ℕ, 2 ≤ Y ∧ ∀ h y w : ℕ, Y ≤ y → y ≤ w →
      Real.log w ≤ Real.exp (θ / 2) * Real.log y →
        (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p) ≤ θ + ε := by
  have hgrowth : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Y, hY⟩ := eventually_atTop.mp (hgrowth.eventually (eventually_ge_atTop (28 / ε)))
  refine ⟨max Y 2, by omega, ?_⟩
  intro h y w hy hyw hratio
  have hy2 : 2 ≤ y := by omega
  have hly : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hlw : 0 < Real.log w := Real.log_pos (by exact_mod_cast (by omega : 1 < w))
  have herr : 28 / Real.log y ≤ ε := by
    apply (div_le_iff₀ hly).mpr
    have hh := mul_le_mul_of_nonneg_right (hY y (by omega)) hε.le
    rw [div_mul_cancel₀ _ hε.ne'] at hh
    linarith
  have hquot : Real.log w / Real.log y ≤ Real.exp (θ / 2) := (div_le_iff₀ hly).mpr hratio
  have hlog := Real.log_le_log (div_pos hlw hly) hquot
  rw [Real.log_exp] at hlog
  have hmain := decompJ365_pair_block_mass_upper h y w hy2 hyw
  linarith

/-- Second memoir page 95: Newton's identity at degree two gives the exact
quadratic error in the factorial approximation to the prime block main sum. -/
lemma decompJ365_esymm_two (x : ℕ → ℝ) (P : Finset ℕ) :
    2 * esymm x P 2 = (∑ p ∈ P, x p) ^ 2 - ∑ p ∈ P, (x p) ^ 2 := by
  have hone (Q : Finset ℕ) : esymm x Q 1 = ∑ p ∈ Q, x p := by
    induction Q using Finset.induction_on with
    | empty => rw [esymm_empty_succ x 0]; simp
    | insert a Q ha ih =>
      rw [esymm_succ_insert x ha 0, esymm_zero, ih, sum_insert ha]
      ring
  induction P using Finset.induction_on with
  | empty => rw [esymm_empty_succ x 1]; simp
  | insert a P ha ih =>
    rw [esymm_succ_insert x ha 1, hone, sum_insert ha, sum_insert ha]
    nlinarith

/-- Second memoir page 95, auxiliary symmetric sum recurrence.
Marking one element of a subset counts each subset once per element. -/
lemma decompJ365_esymm_erase_sum (x : ℕ → ℝ) (P : Finset ℕ) (r : ℕ) :
    (∑ p ∈ P, x p * esymm x (P.erase p) r) = (r + 1) * esymm x P (r + 1) := by
  induction P using Finset.induction_on generalizing r with
  | empty => simp [esymm_empty_succ]
  | insert a P ha ih =>
    cases r with
    | zero =>
      simp only [esymm_zero, mul_one, Nat.cast_zero, zero_add, one_mul]
      have hone (Q : Finset ℕ) : esymm x Q 1 = ∑ p ∈ Q, x p := by
        induction Q using Finset.induction_on with
        | empty => simp [esymm_empty_succ]
        | insert b Q hb hih => rw [esymm_succ_insert x hb 0, esymm_zero, hih, sum_insert hb]; ring
      exact (hone _).symm
    | succ r =>
      rw [sum_insert ha, erase_insert ha, esymm_succ_insert x ha (r + 1)]
      have he (p : ℕ) (hp : p ∈ P) :
          esymm x ((insert a P).erase p) (r + 1) =
            esymm x (P.erase p) (r + 1) + x a * esymm x (P.erase p) r := by
        rw [erase_insert_of_ne (ne_of_mem_of_not_mem hp ha).symm,
          esymm_succ_insert x (fun h => ha (mem_of_mem_erase h))]
      have hsums : (∑ p ∈ P, x p * esymm x ((insert a P).erase p) (r + 1)) =
          ∑ p ∈ P, (x p * esymm x (P.erase p) (r + 1) + x p * (x a * esymm x (P.erase p) r)) := by
        apply sum_congr rfl
        intro p hp
        rw [he p hp, mul_add]
      rw [hsums, sum_add_distrib]
      rw [ih (r + 1)]
      have hs : (∑ p ∈ P, x p * (x a * esymm x (P.erase p) r)) =
          x a * ((r + 1) * esymm x P (r + 1)) := by
        rw [← ih r, mul_sum]
        apply sum_congr rfl
        intro p hp
        ring
      rw [hs]
      push_cast
      ring

/-- Second memoir page 95, auxiliary symmetric sum collision estimate. -/
lemma decompJ365_esymm_collision_identity (x : ℕ → ℝ) (P : Finset ℕ) (r : ℕ) :
    (∑ p ∈ P, x p) * esymm x P (r + 1) =
      (r + 2) * esymm x P (r + 2) +
        ∑ p ∈ P, (x p) ^ 2 * esymm x (P.erase p) r := by
  have hsplit (p : ℕ) (hp : p ∈ P) :
      esymm x P (r + 1) = esymm x (P.erase p) (r + 1) +
        x p * esymm x (P.erase p) r := by
    simpa only [insert_erase hp] using
      esymm_succ_insert x (notMem_erase p P) r
  rw [sum_mul]
  calc
    _ = ∑ p ∈ P, (x p * esymm x (P.erase p) (r + 1) +
        (x p) ^ 2 * esymm x (P.erase p) r) := by
      apply sum_congr rfl
      intro p hp
      rw [hsplit p hp]
      ring
    _ = _ := by
      rw [sum_add_distrib, decompJ365_esymm_erase_sum]
      rw [show r + 1 + 1 = r + 2 by omega]
      push_cast
      ring

/-- Second memoir page 95, auxiliary symmetric sum collision estimate. -/
lemma decompJ365_esymm_collision_bound (x : ℕ → ℝ) (hx : ∀ p, 0 ≤ x p)
    (P : Finset ℕ) (r : ℕ) :
    (r.factorial : ℝ) * (∑ p ∈ P, (x p) ^ 2 * esymm x (P.erase p) r) ≤
      (∑ p ∈ P, (x p) ^ 2) * (∑ p ∈ P, x p) ^ r := by
  rw [mul_sum, sum_mul]
  apply sum_le_sum
  intro p hp
  have hs : (∑ q ∈ P.erase p, x q) ≤ ∑ q ∈ P, x q := by
    exact sum_le_sum_of_subset_of_nonneg (erase_subset p P) (fun q _ _ => hx q)
  have hpow : (∑ q ∈ P.erase p, x q) ^ r ≤ (∑ q ∈ P, x q) ^ r :=
    pow_le_pow_left₀ (sum_nonneg fun q _ => hx q) hs r
  have he := (factorial_mul_esymm_le x hx (P.erase p) r).trans hpow
  nlinarith [mul_le_mul_of_nonneg_left he (sq_nonneg (x p))]

/-- Second memoir page 95, auxiliary symmetric sum collision estimate. -/
lemma decompJ365_esymm_lower_add_two (x : ℕ → ℝ) (hx : ∀ p, 0 ≤ x p)
    (P : Finset ℕ) (r : ℕ) :
    (∑ p ∈ P, x p) ^ (r + 2) - ((r + 2).choose 2 : ℝ) *
      (∑ p ∈ P, x p) ^ r * (∑ p ∈ P, (x p) ^ 2) ≤
        ((r + 2).factorial : ℝ) * esymm x P (r + 2) := by
  have ht : 0 ≤ ∑ p ∈ P, x p := sum_nonneg fun p _ => hx p
  induction r with
  | zero =>
    have hrec := decompJ365_esymm_collision_identity x P 0
    have hone := decompJ365_esymm_erase_sum x P 0
    simp only [esymm_zero, mul_one, Nat.cast_zero, zero_add, one_mul] at hone
    norm_num [esymm_zero] at hrec ⊢
    rw [← hone] at hrec
    nlinarith
  | succ r ih =>
    have hrec := decompJ365_esymm_collision_identity x P (r + 1)
    have hbound := decompJ365_esymm_collision_bound x hx P (r + 1)
    have hmul := mul_le_mul_of_nonneg_left ih ht
    have hmul' := mul_le_mul_of_nonneg_left hbound (show (0 : ℝ) ≤ r + 2 by positivity)
    have hchoose : ((r + 1 + 2).choose 2 : ℝ) = ((r + 2).choose 2 : ℝ) + (r + 2) := by
      rw [show r + 1 + 2 = (r + 2) + 1 by omega, Nat.choose_succ_succ']
      simp only [Nat.choose_one_right, Nat.cast_add]
      ring
    have hf : ((r + 2).factorial : ℝ) = (r + 2) * ((r + 1).factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hf' : ((r + 1 + 2).factorial : ℝ) =
        (r + 3) * ((r + 2).factorial : ℝ) := by
      rw [show r + 1 + 2 = (r + 2) + 1 by omega, Nat.factorial_succ]
      push_cast
      ring
    have hc : ((r + 2).factorial : ℝ) *
        (∑ p ∈ P, (x p) ^ 2 * esymm x (P.erase p) (r + 1)) ≤
          (r + 2) * ((∑ p ∈ P, (x p) ^ 2) * (∑ p ∈ P, x p) ^ (r + 1)) := by
      calc
        _ = (r + 2) * (((r + 1).factorial : ℝ) *
            (∑ p ∈ P, (x p) ^ 2 * esymm x (P.erase p) (r + 1))) := by rw [hf]; ring
        _ ≤ _ := hmul'
    calc
      _ = (∑ p ∈ P, x p) * ((∑ p ∈ P, x p) ^ (r + 2) -
          ((r + 2).choose 2 : ℝ) * (∑ p ∈ P, x p) ^ r * (∑ p ∈ P, (x p) ^ 2)) -
            (r + 2) * ((∑ p ∈ P, (x p) ^ 2) * (∑ p ∈ P, x p) ^ (r + 1)) := by
        rw [hchoose]
        ring
      _ ≤ (∑ p ∈ P, x p) * (((r + 2).factorial : ℝ) * esymm x P (r + 2)) -
          ((r + 2).factorial : ℝ) *
            (∑ p ∈ P, (x p) ^ 2 * esymm x (P.erase p) (r + 1)) := sub_le_sub hmul hc
      _ = _ := by
        rw [hf']
        have hrec' := congrArg (fun z : ℝ => ((r + 2).factorial : ℝ) * z) hrec
        simp only [Nat.cast_add, Nat.cast_one] at hrec'
        rw [show r + 1 + 1 = r + 2 by omega] at hrec'
        linear_combination hrec'

/-- Second memoir page 95, auxiliary symmetric sum collision estimate. -/
lemma decompJ365_esymm_bounds (x : ℕ → ℝ) (hx : ∀ p, 0 ≤ x p)
    (P : Finset ℕ) (r : ℕ) :
    (∑ p ∈ P, x p) ^ r - (r.choose 2 : ℝ) *
      (∑ p ∈ P, x p) ^ (r - 2) * (∑ p ∈ P, (x p) ^ 2) ≤
        (r.factorial : ℝ) * esymm x P r ∧
      (r.factorial : ℝ) * esymm x P r ≤ (∑ p ∈ P, x p) ^ r := by
  refine ⟨?_, factorial_mul_esymm_le x hx P r⟩
  rcases r with _ | r
  · simp [esymm_zero]
  rcases r with _ | r
  · have h := decompJ365_esymm_erase_sum x P 0
    simpa [esymm_zero] using h.le
  · simpa using decompJ365_esymm_lower_add_two x hx P r

/-- Second memoir page 95, auxiliary symmetric sum collision estimate. -/
lemma decompJ365_esymm_approx (x : ℕ → ℝ) (hx : ∀ p, 0 ≤ x p)
    (P : Finset ℕ) (r : ℕ) :
    |esymm x P r - (∑ p ∈ P, x p) ^ r / (r.factorial : ℝ)| ≤
      (r.choose 2 : ℝ) * (∑ p ∈ P, x p) ^ (r - 2) *
        (∑ p ∈ P, (x p) ^ 2) / (r.factorial : ℝ) := by
  obtain ⟨hl, hu⟩ := decompJ365_esymm_bounds x hx P r
  have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ((le_div_iff₀ hf).mpr (by nlinarith)))]
  apply (le_div_iff₀ hf).mpr
  rw [sub_mul, div_mul_cancel₀ _ hf.ne']
  nlinarith

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_pair_block_square_upper (h y w : ℕ) (hy : 0 < y) :
    (∑ p ∈ (Ioc y w).filter Nat.Prime, (nuN h p) ^ 2) ≤
      (2 / (y : ℝ)) * ∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p := by
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  obtain ⟨hpI, hpP⟩ := mem_filter.mp hp
  have hyp : (y : ℝ) ≤ p := by exact_mod_cast (mem_Ioc.mp hpI).1.le
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hpR : (0 : ℝ) < p := hyR.trans_le hyp
  have hnu : nuN h p ≤ 2 / (y : ℝ) := by
    rw [nuN_prime hpP]
    exact (div_le_div_of_nonneg_right (wt_le_two h p) hpR.le).trans
      (div_le_div_of_nonneg_left (by norm_num) hyR hyp)
  nlinarith [mul_le_mul_of_nonneg_right hnu (nuN_nonneg h p)]

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_pair_block_square_eventually (θ ε : ℝ) (hε : 0 < ε) :
    ∃ Y : ℕ, 2 ≤ Y ∧ ∀ h y w : ℕ, Y ≤ y → y ≤ w →
      Real.log w ≤ Real.exp (θ / 2) * Real.log y →
        (∑ p ∈ (Ioc y w).filter Nat.Prime, (nuN h p) ^ 2) ≤ ε := by
  obtain ⟨Y₁, hY₁, hm⟩ := decompJ365_pair_block_mass_eventually θ 1 (by norm_num)
  obtain ⟨Y₂, hY₂⟩ := exists_nat_ge (2 * max (θ + 1) 0 / ε)
  refine ⟨max Y₁ Y₂, le_trans hY₁ (le_max_left _ _), ?_⟩
  intro h y w hy hyw hr
  have hy2 : 2 ≤ y := hY₁.trans ((le_max_left _ _).trans hy)
  have hyR : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hm' := hm h y w ((le_max_left _ _).trans hy) hyw hr
  have hlarge : 2 * max (θ + 1) 0 / ε ≤ (y : ℝ) :=
    hY₂.trans (by exact_mod_cast ((le_max_right Y₁ Y₂).trans hy))
  calc
    _ ≤ 2 / (y : ℝ) * (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p) :=
      decompJ365_pair_block_square_upper h y w (by omega)
    _ ≤ 2 / (y : ℝ) * max (θ + 1) 0 :=
      mul_le_mul_of_nonneg_left (hm'.trans (le_max_left _ _)) (by positivity)
    _ ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hyR]
      have hh := (div_le_iff₀ hε).mp hlarge
      nlinarith

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_nested_layer_bound (S : Finset ℕ) (f : ℕ → ℝ) (u : ℕ → ℝ)
    (hu : ∀ i, u (i + 1) ≤ u i) (hf : ∀ p ∈ S, f p ≤ u 0) (n : ℕ) :
    (∑ p ∈ S, f p) ≤ (S.card : ℝ) * u n +
      ∑ i ∈ range n, (u i - u (i + 1)) * (S.filter (fun p => u (i + 1) < f p)).card := by
  have hpoint (a : ℝ) (ha : a ≤ u 0) (k : ℕ) :
      a ≤ u k + ∑ i ∈ range k, if u (i + 1) < a then u i - u (i + 1) else 0 := by
    induction k with
    | zero => simpa using ha
    | succ k ih =>
      rw [sum_range_succ]
      by_cases h : u (k + 1) < a
      · rw [ite_eq_left h]
        linarith
      · rw [ite_eq_right h, add_zero]
        have hsum : 0 ≤ ∑ i ∈ range k,
            if u (i + 1) < a then u i - u (i + 1) else 0 := by
          apply sum_nonneg
          intro i hi
          split_ifs
          · exact sub_nonneg.mpr (hu i)
          · exact le_rfl
        linarith
  calc
    _ ≤ ∑ p ∈ S, (u n + ∑ i ∈ range n,
        if u (i + 1) < f p then u i - u (i + 1) else 0) :=
      sum_le_sum (fun p hp => hpoint (f p) (hf p hp) n)
    _ = _ := by
      rw [sum_add_distrib, sum_const, nsmul_eq_mul, sum_comm]
      congr 1
      apply sum_congr rfl
      intro i hi
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul]
      ring

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_nested_log_support (S : Finset ℕ) (f : ℕ → ℝ) (u : ℕ → ℝ)
    (hu : ∀ i, u (i + 1) ≤ u i) (hf : ∀ p ∈ S, f p ≤ u 0)
    (n : ℕ) (hn : 0 ≤ u n) (hc : S.card ≤ 2 * n + 1)
    (hcap : ∀ i ∈ range n, (S.filter (fun p => u (i + 1) < f p)).card ≤ 2 * i + 1) :
    (∑ p ∈ S, f p) ≤ u 0 + 2 * ∑ i ∈ range n, u (i + 1) := by
  have htel (k : ℕ) : ((2 * k + 1 : ℕ) : ℝ) * u k +
      (∑ i ∈ range k, (u i - u (i + 1)) * (2 * i + 1 : ℕ)) =
        u 0 + 2 * ∑ i ∈ range k, u (i + 1) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ, sum_range_succ]
      push_cast at ih ⊢
      linear_combination ih
  calc
    _ ≤ (S.card : ℝ) * u n +
        ∑ i ∈ range n, (u i - u (i + 1)) * (S.filter (fun p => u (i + 1) < f p)).card :=
      decompJ365_nested_layer_bound S f u hu hf n
    _ ≤ ((2 * n + 1 : ℕ) : ℝ) * u n +
        ∑ i ∈ range n, (u i - u (i + 1)) * (2 * i + 1 : ℕ) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hn
      · apply sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcap i hi) (sub_nonneg.mpr (hu i))
    _ = _ := htel n

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_nested_power_support (S : Finset ℕ) (T : ℝ) (hT : 1 < T)
    (α : ℕ → ℝ) (hα : ∀ i, α (i + 1) ≤ α i) (n : ℕ) (hn : 0 ≤ α n)
    (hp : ∀ p ∈ S, 0 < p) (hmax : ∀ p ∈ S, (p : ℝ) ≤ T ^ (α 0))
    (hc : S.card ≤ 2 * n + 1)
    (hcap : ∀ i ∈ range n,
      (S.filter (fun p : ℕ => T ^ (α (i + 1)) < (p : ℝ))).card ≤ 2 * i + 1) :
    ((∏ p ∈ S, p : ℕ) : ℝ) ≤ T ^ (α 0 + 2 * ∑ i ∈ range n, α (i + 1)) := by
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have hpR : ∀ p ∈ S, (0 : ℝ) < p := fun p h => by exact_mod_cast hp p h
  have hupper : ∀ p ∈ S, Real.log (p : ℝ) ≤ α 0 * Real.log T := by
    intro p h
    have hl := Real.log_le_log (hpR p h) (hmax p h)
    rwa [Real.log_rpow hT0] at hl
  have hfilters (i : ℕ) : S.filter (fun p : ℕ => α (i + 1) * Real.log T < Real.log (p : ℝ)) =
      S.filter (fun p : ℕ => T ^ (α (i + 1)) < (p : ℝ)) := by
    apply filter_congr
    intro p hpS
    rw [← Real.log_rpow hT0]
    exact Real.log_lt_log_iff (Real.rpow_pos_of_pos hT0 _) (hpR p hpS)
  have hs := decompJ365_nested_log_support S (fun p => Real.log (p : ℝ))
    (fun i => α i * Real.log T)
    (fun i => mul_le_mul_of_nonneg_right (hα i) hlogT.le)
    hupper n (mul_nonneg hn hlogT.le) hc (by simpa only [hfilters] using hcap)
  have hprod : (0 : ℝ) < ∏ p ∈ S, (p : ℝ) := prod_pos hpR
  have hlogprod : Real.log (∏ p ∈ S, (p : ℝ)) = ∑ p ∈ S, Real.log (p : ℝ) :=
    Real.log_prod (fun p h => (hpR p h).ne')
  have hexp : ∏ p ∈ S, (p : ℝ) ≤
      Real.exp ((α 0 + 2 * ∑ i ∈ range n, α (i + 1)) * Real.log T) := by
    rw [← Real.exp_log hprod, Real.exp_le_exp, hlogprod]
    simpa only [add_mul, mul_assoc, sum_mul] using hs
  simpa only [Nat.cast_prod, Real.rpow_def_of_pos hT0, mul_comm (Real.log T)] using hexp

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_nested_saved_support (S : Finset ℕ) (N T δ τ κ : ℝ)
    (hN : 1 ≤ N) (hT : 1 < T) (hTN : T ≤ N ^ δ) (hτ : 0 ≤ τ) (_hκ : 0 < κ)
    (α : ℕ → ℝ) (hα : ∀ i, α (i + 1) ≤ α i) (hα₀ : α 0 = 1)
    (n : ℕ) (hn : 0 ≤ α n) (hsum : (∑ i ∈ range n, α (i + 1)) ≤ τ)
    (hp : ∀ p ∈ S, 0 < p) (hmax : ∀ p ∈ S, (p : ℝ) ≤ T)
    (hc : S.card ≤ 2 * n + 1)
    (hcap : ∀ i ∈ range n,
      (S.filter (fun p : ℕ => T ^ (α (i + 1)) < (p : ℝ))).card ≤ 2 * i + 1)
    (hsave : δ * (1 + 2 * τ) ≤ 1 - κ) :
    ((∏ p ∈ S, p : ℕ) : ℝ) ≤ N ^ (1 - κ) := by
  have hs := decompJ365_nested_power_support S T hT α hα n hn hp
    (by simpa only [hα₀, Real.rpow_one] using hmax) hc hcap
  rw [hα₀] at hs
  calc
    _ ≤ T ^ (1 + 2 * ∑ i ∈ range n, α (i + 1)) := hs
    _ ≤ T ^ (1 + 2 * τ) := Real.rpow_le_rpow_of_exponent_le hT.le (by linarith)
    _ ≤ (N ^ δ) ^ (1 + 2 * τ) :=
      Real.rpow_le_rpow (le_trans zero_le_one hT.le) hTN (by positivity)
    _ = N ^ (δ * (1 + 2 * τ)) := (Real.rpow_mul (le_trans zero_le_one hN) _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN hsave

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_choose_saved_exponent (A B C E : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (_hE : 0 < E)
    (hCA : C < A) (hECB : E * C < B) :
    ∃ δ κ : ℝ, 0 < δ ∧ 0 < κ ∧ 1 / A < δ ∧ E / B < δ ∧ δ * C ≤ 1 - κ := by
  have h₁ : 1 / A < 1 / C := one_div_lt_one_div_of_lt hC hCA
  have h₂ : E / B < 1 / C := (div_lt_div_iff₀ hB hC).mpr (by simpa using hECB)
  obtain ⟨δ, hδlo, hδhi⟩ := exists_between (max_lt h₁ h₂)
  have hδC : δ * C < 1 := (lt_div_iff₀ hC).mp hδhi
  refine ⟨δ, 1 - δ * C, ?_, by linarith, ?_, ?_, by linarith⟩
  · exact (div_pos zero_lt_one hA).trans ((le_max_left _ _).trans_lt hδlo)
  · exact (le_max_left _ _).trans_lt hδlo
  · exact (le_max_right _ _).trans_lt hδlo

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_esymm_tendsto (x : ℕ → ℕ → ℝ) (P : ℕ → Finset ℕ)
    (hx : ∀ n p, 0 ≤ x n p) (t : ℝ)
    (ht : Tendsto (fun n => ∑ p ∈ P n, x n p) atTop (nhds t))
    (hq : Tendsto (fun n => ∑ p ∈ P n, (x n p) ^ 2) atTop (nhds 0)) (r : ℕ) :
    Tendsto (fun n => esymm (x n) (P n) r) atTop (nhds (t ^ r / (r.factorial : ℝ))) := by
  have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hl : Tendsto (fun n => ((∑ p ∈ P n, x n p) ^ r -
      (r.choose 2 : ℝ) * (∑ p ∈ P n, x n p) ^ (r - 2) *
        (∑ p ∈ P n, (x n p) ^ 2)) / (r.factorial : ℝ)) atTop
          (nhds (t ^ r / (r.factorial : ℝ))) := by
    simpa using ((ht.pow r).sub (((tendsto_const_nhds.mul (ht.pow (r - 2))).mul hq))).div_const
      (r.factorial : ℝ)
  have hu := (ht.pow r).div_const (r.factorial : ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu
  · intro n
    have h := (decompJ365_esymm_bounds (x n) (hx n) (P n) r).1
    exact (div_le_iff₀ hf).mpr (by nlinarith)
  · intro n
    have h := (decompJ365_esymm_bounds (x n) (hx n) (P n) r).2
    exact (le_div_iff₀ hf).mpr (by nlinarith)

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_lower_head_identity_cast (t₁ t₂ t₃ : ℚ) :
    (∑ i ∈ range 2, ∑ j ∈ range 4, ∑ k ∈ range 6,
      if i + j ≤ 3 ∧ i + j + k ≤ 5 then
        (-1 : ℝ) ^ (i + j + k) * ((t₁ : ℝ) ^ i / (i.factorial : ℝ)) *
          ((t₂ : ℝ) ^ j / (j.factorial : ℝ)) * ((t₃ : ℝ) ^ k / (k.factorial : ℝ)) else 0) =
      (Ebar3 t₁ t₂ t₃ : ℝ) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (decompJ365_lower_head_identity t₁ t₂ t₃)
  push_cast at h
  simp only [apply_ite] at h
  push_cast at h
  exact h

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_lower_head_tendsto (x : ℕ → ℕ → ℝ)
    (P₁ P₂ P₃ : ℕ → Finset ℕ) (hx : ∀ n p, 0 ≤ x n p) (t₁ t₂ t₃ : ℚ)
    (ht₁ : Tendsto (fun n => ∑ p ∈ P₁ n, x n p) atTop (nhds (t₁ : ℝ)))
    (ht₂ : Tendsto (fun n => ∑ p ∈ P₂ n, x n p) atTop (nhds (t₂ : ℝ)))
    (ht₃ : Tendsto (fun n => ∑ p ∈ P₃ n, x n p) atTop (nhds (t₃ : ℝ)))
    (hq₁ : Tendsto (fun n => ∑ p ∈ P₁ n, (x n p) ^ 2) atTop (nhds 0))
    (hq₂ : Tendsto (fun n => ∑ p ∈ P₂ n, (x n p) ^ 2) atTop (nhds 0))
    (hq₃ : Tendsto (fun n => ∑ p ∈ P₃ n, (x n p) ^ 2) atTop (nhds 0)) :
    Tendsto (fun n => ∑ i ∈ range 2, ∑ j ∈ range 4, ∑ k ∈ range 6,
      if i + j ≤ 3 ∧ i + j + k ≤ 5 then
        (-1 : ℝ) ^ (i + j + k) * esymm (x n) (P₁ n) i *
          esymm (x n) (P₂ n) j * esymm (x n) (P₃ n) k else 0)
      atTop (nhds (Ebar3 t₁ t₂ t₃ : ℝ)) := by
  rw [← decompJ365_lower_head_identity_cast]
  apply tendsto_finsetSum
  intro i hi
  apply tendsto_finsetSum
  intro j hj
  apply tendsto_finsetSum
  intro k hk
  by_cases hc : i + j ≤ 3 ∧ i + j + k ≤ 5
  · simp only [ite_eq_left hc]
    exact ((tendsto_const_nhds.mul (decompJ365_esymm_tendsto x P₁ hx t₁ ht₁ hq₁ i)).mul
      (decompJ365_esymm_tendsto x P₂ hx t₂ ht₂ hq₂ j)).mul
        (decompJ365_esymm_tendsto x P₃ hx t₃ ht₃ hq₃ k)
  · simp only [ite_eq_right hc]
    exact tendsto_const_nhds

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_first_four_saved_exponents :
    let t₂ := exp (-(log (4 / 3 : ℝ)) / 2) * ricciTau 2
    let t₃ := exp (-(log (2 : ℝ)) / 2) * ricciTau 2
    let t₄ := exp (-0.90 : ℝ) + exp (-(log (4 : ℝ)) / 2) *
      (exp (-1.46 / 2) + exp (-1.98 / 2) / (1 - exp (-0.50 / 2)))
    (∃ δ κ : ℝ, 0 < δ ∧ 0 < κ ∧ 1 / 7 < δ ∧ 1 / 7 < δ ∧
      δ * (1 + 2 * ricciTau 2 + 2 * 0.001) ≤ 1 - κ) ∧
    (∃ δ κ : ℝ, 0 < δ ∧ 0 < κ ∧ 1 / 6 < δ ∧ (4 / 3 : ℝ) / 8 < δ ∧
      δ * (1 + 2 * t₂ + 2 * 0.001) ≤ 1 - κ) ∧
    (∃ δ κ : ℝ, 0 < δ ∧ 0 < κ ∧ 1 / 5 < δ ∧ (2 : ℝ) / 10 < δ ∧
      δ * (1 + 2 * t₃ + 2 * 0.001) ≤ 1 - κ) ∧
    (∃ δ κ : ℝ, 0 < δ ∧ 0 < κ ∧ 1 / 4 < δ ∧ (4 : ℝ) / 16 < δ ∧
      δ * (1 + 2 * t₄ + 2 * 0.001) ≤ 1 - κ) := by
  have hd : 0 < 1 - exp (-0.50 / 2 : ℝ) := by
    apply sub_pos.mpr
    exact exp_lt_one_iff.mpr (by norm_num)
  have ht : 0 ≤ ricciTau 2 := by unfold ricciTau; positivity
  have hm := decompJ365_first_four_margins
  dsimp only at hm ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using decompJ365_choose_saved_exponent 7 7
      (1 + 2 * ricciTau 2 + 2 * 0.001) 1
      (by norm_num) (by norm_num) (by positivity) (by norm_num) hm.1
      (by simpa using hm.1)
  · exact decompJ365_choose_saved_exponent 6 8
      (1 + 2 * (exp (-(log (4 / 3 : ℝ)) / 2) * ricciTau 2) + 2 * 0.001) (4 / 3)
      (by norm_num) (by norm_num) (by positivity) (by norm_num) hm.2.1.1 hm.2.1.2
  · exact decompJ365_choose_saved_exponent 5 10
      (1 + 2 * (exp (-(log (2 : ℝ)) / 2) * ricciTau 2) + 2 * 0.001) 2
      (by norm_num) (by norm_num) (by positivity) (by norm_num) hm.2.2.1.1 hm.2.2.1.2
  · exact decompJ365_choose_saved_exponent 4 16
      (1 + 2 * (exp (-0.90 : ℝ) + exp (-(log (4 : ℝ)) / 2) *
        (exp (-1.46 / 2) + exp (-1.98 / 2) / (1 - exp (-0.50 / 2)))) + 2 * 0.001) 4
      (by norm_num) (by norm_num) (by positivity) (by norm_num) hm.2.2.2.1 hm.2.2.2.2

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_pair_block_mass_unbounded (Y : ℕ) (t : ℝ) :
    ∃ W : ℕ, Y ≤ W ∧ ∀ h w : ℕ, W ≤ w →
      t ≤ ∑ p ∈ (Ioc Y w).filter Nat.Prime, nuN h p := by
  let f : ℕ → ℝ := Set.indicator {p | p.Prime} (fun p => (1 : ℝ) / p)
  have hf0 : ∀ p, 0 ≤ f p := fun p => Set.indicator_nonneg (fun q _ => by positivity) p
  have hdiv : Tendsto (fun z : ℕ => ∑ p ∈ range z, f p) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hf0).mp not_summable_one_div_on_primes
  obtain ⟨W, hW⟩ := eventually_atTop.mp
    (hdiv.eventually (eventually_ge_atTop (t + ∑ p ∈ range (Y + 1), f p)))
  refine ⟨max Y W, le_max_left _ _, ?_⟩
  intro h w hw
  have hYw : Y ≤ w := (le_max_left _ _).trans hw
  have hbig := hW (w + 1) (by omega)
  have hsplit : (∑ p ∈ range (Y + 1), f p) + (∑ p ∈ Ioc Y w, f p) =
      ∑ p ∈ range (w + 1), f p := by
    have hsets : Ioc Y w = Ico (Y + 1) (w + 1) := by ext p; simp only [mem_Ioc, mem_Ico]; omega
    rw [hsets]
    simpa using sum_Ico_consecutive f (Nat.zero_le (Y + 1)) (by omega : Y + 1 ≤ w + 1)
  have hs : (∑ p ∈ Ioc Y w, f p) =
      ∑ p ∈ (Ioc Y w).filter Nat.Prime, (1 : ℝ) / p := by
    rw [sum_filter]
    apply sum_congr rfl
    intro p hp
    by_cases hpp : p.Prime <;> simp [f, hpp]
  have hlow : (∑ p ∈ (Ioc Y w).filter Nat.Prime, (1 : ℝ) / p) ≤
      ∑ p ∈ (Ioc Y w).filter Nat.Prime, nuN h p := by
    apply sum_le_sum
    intro p hp
    rw [nuN_prime (mem_filter.mp hp).2]
    exact div_le_div_of_nonneg_right (one_le_wt h p) (Nat.cast_nonneg p)
  rw [hs] at hsplit
  linarith

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_pair_block_choose (h Y w : ℕ) (hY : 0 < Y) (hYw : Y ≤ w)
    (t : ℝ) (ht : 0 < t)
    (hmass : t < ∑ p ∈ (Ioc Y w).filter Nat.Prime, nuN h p) :
    ∃ y : ℕ, Y < y ∧ y ≤ w ∧
      t - 2 / (Y : ℝ) < (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p) ∧
        (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p) ≤ t := by
  have hex : ∃ y : ℕ, Y ≤ y ∧ y ≤ w ∧
      (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p) ≤ t := by
    exact ⟨w, hYw, le_rfl, by simpa using ht.le⟩
  let y := Nat.find hex
  obtain ⟨hYy, hyw, hym⟩ := Nat.find_spec hex
  change Y ≤ y at hYy
  change y ≤ w at hyw
  change (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p) ≤ t at hym
  have hYy' : Y < y := by
    by_contra h
    have heq : y = Y := by omega
    rw [heq] at hym
    linarith
  have hyprev : t < ∑ p ∈ (Ioc (y - 1) w).filter Nat.Prime, nuN h p := by
    have hmin := Nat.find_min hex (show y - 1 < y by omega)
    have hcond : Y ≤ y - 1 ∧ y - 1 ≤ w := by omega
    exact lt_of_not_ge (fun hm => hmin ⟨hcond.1, hcond.2, hm⟩)
  have hsplit : Ioc (y - 1) w = insert y (Ioc y w) := by
    ext p
    simp only [mem_Ioc, mem_insert]
    omega
  have hnot : y ∉ (Ioc y w).filter Nat.Prime := by simp
  have hyR : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  have hstep : (∑ p ∈ (Ioc (y - 1) w).filter Nat.Prime, nuN h p) ≤
      (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p) + 2 / (Y : ℝ) := by
    rw [hsplit, filter_insert]
    by_cases hprime : y.Prime
    · rw [ite_eq_left hprime, sum_insert hnot]
      have hnu : nuN h y ≤ 2 / (Y : ℝ) := by
        rw [nuN_prime hprime]
        exact (div_le_div_of_nonneg_right (wt_le_two h y) hyR.le).trans
          (div_le_div_of_nonneg_left (by norm_num) hYR (by exact_mod_cast hYy))
      linarith
    · rw [ite_eq_right hprime]
      exact le_add_of_nonneg_right (by positivity)
  exact ⟨y, hYy', hyw, by linarith, hym⟩

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_pair_block_cutoff_upper (h y w : ℕ) (θ ε : ℝ)
    (hy : 2 ≤ y) (hyw : y ≤ w)
    (hmass : θ - ε ≤ ∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p)
    (hend : 28 / Real.log y ≤ ε) :
    (y : ℝ) ≤ (w : ℝ) ^ Real.exp (-θ / 2 + ε) := by
  have hyR : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hwR : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have hly : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hlw : 0 < Real.log w := Real.log_pos (by exact_mod_cast (by omega : 1 < w))
  have hmain := decompJ365_pair_block_mass_upper h y w hy hyw
  have hl : θ / 2 - ε ≤ Real.log (Real.log w / Real.log y) := by linarith
  have hexp : Real.exp (θ / 2 - ε) ≤ Real.log w / Real.log y := by
    simpa only [Real.exp_log (div_pos hlw hly)] using Real.exp_le_exp.mpr hl
  have hm := (le_div_iff₀ hly).mp hexp
  have hm' := mul_le_mul_of_nonneg_left hm (Real.exp_pos (-θ / 2 + ε)).le
  have he : Real.exp (-θ / 2 + ε) * Real.exp (θ / 2 - ε) = 1 := by
    rw [← Real.exp_add]
    rw [show (-θ / 2 + ε) + (θ / 2 - ε) = 0 by ring, Real.exp_zero]
  rw [← mul_assoc, he, one_mul] at hm'
  apply (Real.log_le_log_iff hyR (Real.rpow_pos_of_pos hwR _)).mp
  rwa [Real.log_rpow hwR]

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_pair_block_choose_eventually (θ ε : ℝ) (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ Y : ℕ, 2 ≤ Y ∧ ∀ Z : ℕ, Y ≤ Z → ∃ W : ℕ, Z ≤ W ∧
      ∀ h w : ℕ, W ≤ w → ∃ y : ℕ, Z < y ∧ y ≤ w ∧
        θ - ε < (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p) ∧
        (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p) ≤ θ ∧
        (y : ℝ) ≤ (w : ℝ) ^ Real.exp (-θ / 2 + ε) := by
  have hgrowth : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.mp
    (hgrowth.eventually (eventually_ge_atTop (28 / ε)))
  obtain ⟨Y₂, hY₂⟩ := exists_nat_ge (2 / ε)
  refine ⟨max (max Y₁ Y₂) 2, le_max_right _ _, ?_⟩
  intro Z hZ
  have hZ2 : 2 ≤ Z := (le_max_right _ _).trans hZ
  have hZR : (0 : ℝ) < Z := by exact_mod_cast (by omega : 0 < Z)
  have hlarge : 2 / ε ≤ (Z : ℝ) := hY₂.trans (by
    exact_mod_cast ((le_max_right Y₁ Y₂).trans ((le_max_left (max Y₁ Y₂) 2).trans hZ)))
  have hsmall : 2 / (Z : ℝ) ≤ ε := by
    rw [div_le_iff₀ hZR]
    have hh := (div_le_iff₀ hε).mp hlarge
    linarith
  obtain ⟨W, hW, hm⟩ := decompJ365_pair_block_mass_unbounded Z (θ + 1)
  refine ⟨W, hW, ?_⟩
  intro h w hw
  have hmass : θ < ∑ p ∈ (Ioc Z w).filter Nat.Prime, nuN h p := by
    have hh := hm h w hw
    linarith
  obtain ⟨y, hZy, hyw, hlo, hhi⟩ := decompJ365_pair_block_choose h Z w (by omega)
    (hW.trans hw) θ hθ hmass
  have hy2 : 2 ≤ y := by omega
  have hly : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hend : 28 / Real.log y ≤ ε := by
    rw [div_le_iff₀ hly]
    have hh := mul_le_mul_of_nonneg_right (hY₁ y (by omega)) hε.le
    rw [div_mul_cancel₀ _ hε.ne'] at hh
    linarith
  have hlo' : θ - ε < ∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p := by linarith
  exact ⟨y, hZy, hyw, hlo', hhi,
    decompJ365_pair_block_cutoff_upper h y w θ ε hy2 hyw hlo'.le hend⟩

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_pair_block_mass_sequence (h : ℕ → ℕ) (θ : ℝ) (hθ : 0 < θ) :
    ∃ y w : ℕ → ℕ, Tendsto y atTop atTop ∧ (∀ n, y n ≤ w n) ∧
      Tendsto (fun n => ∑ p ∈ (Ioc (y n) (w n)).filter Nat.Prime, nuN (h n) p)
        atTop (nhds θ) ∧
      Tendsto (fun n => ∑ p ∈ (Ioc (y n) (w n)).filter Nat.Prime, (nuN (h n) p) ^ 2)
        atTop (nhds 0) ∧
      ∀ n, (y n : ℝ) ≤ (w n : ℝ) ^ Real.exp (-θ / 2 + 1 / ((n : ℝ) + 1)) := by
  have hchoose (n : ℕ) : ∃ y w : ℕ, n + 2 ≤ y ∧ y ≤ w ∧
      θ - 1 / ((n : ℝ) + 1) < (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN (h n) p) ∧
      (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN (h n) p) ≤ θ ∧
      (y : ℝ) ≤ (w : ℝ) ^ Real.exp (-θ / 2 + 1 / ((n : ℝ) + 1)) := by
    obtain ⟨Y, hY, hYprop⟩ := decompJ365_pair_block_choose_eventually θ
      (1 / ((n : ℝ) + 1)) hθ (by positivity)
    obtain ⟨W, hW, hWprop⟩ := hYprop (max Y (n + 2)) (le_max_left _ _)
    obtain ⟨y, hy, hyW, hlo, hhi, hpow⟩ := hWprop (h n) W le_rfl
    exact ⟨y, W, by omega, hyW, hlo, hhi, hpow⟩
  choose y w hy using hchoose
  have hydiv : Tendsto y atTop atTop :=
    tendsto_atTop_mono (fun n => (hy n).1) (tendsto_add_atTop_nat 2)
  have heps : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hmass : Tendsto (fun n => ∑ p ∈ (Ioc (y n) (w n)).filter Nat.Prime, nuN (h n) p)
      atTop (nhds θ) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using tendsto_const_nhds.sub heps) tendsto_const_nhds
    · intro n
      simpa only [one_div] using (hy n).2.2.1.le
    · intro n
      exact (hy n).2.2.2.1
  have hyR : Tendsto (fun n => (y n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hydiv
  have hbound : Tendsto (fun n => 2 / (y n : ℝ) * θ) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using ((tendsto_inv_atTop_zero.comp hyR).const_mul 2).mul_const θ
  have hsq : Tendsto (fun n => ∑ p ∈ (Ioc (y n) (w n)).filter Nat.Prime, (nuN (h n) p) ^ 2)
      atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    · intro n
      exact sum_nonneg (fun p _ => sq_nonneg _)
    · intro n
      have hypos : 0 < y n := by have := (hy n).1; omega
      calc
        _ ≤ 2 / (y n : ℝ) * ∑ p ∈ (Ioc (y n) (w n)).filter Nat.Prime, nuN (h n) p :=
          decompJ365_pair_block_square_upper (h n) (y n) (w n) hypos
        _ ≤ _ := mul_le_mul_of_nonneg_left (hy n).2.2.2.1 (by positivity)
  exact ⟨y, w, hydiv, fun n => (hy n).2.1, hmass, hsq, fun n => (hy n).2.2.2.2⟩

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_main_positive_of_head_comparison (H M : ℕ → ℝ)
    (hH : Tendsto H atTop (nhds (Ebar3 (90 / 100) (56 / 100) (52 / 100) : ℝ)))
    (hM : ∀ᶠ n : ℕ in atTop,
      exp (0.90 + 0.56 + 0.52) * (H n -
        (0.90 * 0.56 ^ (2 : ℕ) * 0.52 ^ (2 : ℕ) /
          (0.50 ^ (5 : ℕ) * exp (3 * 0.50))) *
        ∑' k : ℕ, ricciBetaBarTerm (exp (0.5 : ℝ) / 4) (4 + k)) ≤ M n) :
    ∀ᶠ n : ℕ in atTop, (0.00066 : ℝ) < M n := by
  have hlim : Tendsto (fun n => exp (0.90 + 0.56 + 0.52) * (H n -
      (0.90 * 0.56 ^ (2 : ℕ) * 0.52 ^ (2 : ℕ) /
        (0.50 ^ (5 : ℕ) * exp (3 * 0.50))) *
      ∑' k : ℕ, ricciBetaBarTerm (exp (0.5 : ℝ) / 4) (4 + k)))
        atTop (nhds ricciSigmaBarLower) := by
    unfold ricciSigmaBarLower
    exact tendsto_const_nhds.mul (hH.sub tendsto_const_nhds)
  have hpos := hlim.eventually (eventually_gt_nhds ricciSigmaBarLower_gt)
  filter_upwards [hM, hpos] with n hn hposn
  exact hposn.trans_le hn

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_three_blocks_choose (ε : ℝ) (hε : 0 < ε) (Z : ℕ) :
    ∃ W : ℕ, Z ≤ W ∧ ∀ h w : ℕ, W ≤ w → ∃ a b c : ℕ,
      Z < c ∧ c ≤ b ∧ b ≤ a ∧ a ≤ w ∧
      (0.90 - ε < (∑ p ∈ (Ioc a w).filter Nat.Prime, nuN h p) ∧
        (∑ p ∈ (Ioc a w).filter Nat.Prime, nuN h p) ≤ 0.90) ∧
      (0.56 - ε < (∑ p ∈ (Ioc b a).filter Nat.Prime, nuN h p) ∧
        (∑ p ∈ (Ioc b a).filter Nat.Prime, nuN h p) ≤ 0.56) ∧
      (0.52 - ε < (∑ p ∈ (Ioc c b).filter Nat.Prime, nuN h p) ∧
        (∑ p ∈ (Ioc c b).filter Nat.Prime, nuN h p) ≤ 0.52) ∧
      (a : ℝ) ≤ (w : ℝ) ^ Real.exp (-0.90 / 2 + ε) ∧
      (b : ℝ) ≤ (a : ℝ) ^ Real.exp (-0.56 / 2 + ε) ∧
      (c : ℝ) ≤ (b : ℝ) ^ Real.exp (-0.52 / 2 + ε) := by
  obtain ⟨Y₃, _, h₃⟩ := decompJ365_pair_block_choose_eventually 0.52 ε (by norm_num) hε
  obtain ⟨W₃, hW₃, h₃'⟩ := h₃ (max Y₃ Z) (le_max_left _ _)
  obtain ⟨Y₂, _, h₂⟩ := decompJ365_pair_block_choose_eventually 0.56 ε (by norm_num) hε
  obtain ⟨W₂, hW₂, h₂'⟩ := h₂ (max Y₂ W₃) (le_max_left _ _)
  obtain ⟨Y₁, _, h₁⟩ := decompJ365_pair_block_choose_eventually 0.90 ε (by norm_num) hε
  obtain ⟨W₁, hW₁, h₁'⟩ := h₁ (max Y₁ W₂) (le_max_left _ _)
  refine ⟨W₁, by omega, ?_⟩
  intro h w hw
  obtain ⟨a, ha, haw, ha₀, ha₁, hap⟩ := h₁' h w hw
  obtain ⟨b, hb, hba, hb₀, hb₁, hbp⟩ := h₂' h a (by omega)
  obtain ⟨c, hc, hcb, hc₀, hc₁, hcp⟩ := h₃' h b (by omega)
  exact ⟨a, b, c, by omega, hcb, hba, haw, ⟨ha₀, ha₁⟩, ⟨hb₀, hb₁⟩,
    ⟨hc₀, hc₁⟩, hap, hbp, hcp⟩

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_tau_support_perturbation (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 4 ∧
      exp (-0.90 / 2 + ε) + exp (-1.46 / 2 + 2 * ε) +
        exp (-1.98 / 2 + 3 * ε) / (1 - exp (-0.50 / 2 + ε)) < ricciTau 2 + η := by
  let g : ℝ → ℝ := fun ε => exp (-0.90 / 2 + ε) + exp (-1.46 / 2 + 2 * ε) +
    exp (-1.98 / 2 + 3 * ε) / (1 - exp (-0.50 / 2 + ε))
  have hd : 1 - exp (-0.50 / 2 : ℝ) ≠ 0 := by
    have he : exp (-0.50 / 2 : ℝ) < 1 := exp_lt_one_iff.mpr (by norm_num)
    linarith
  have hg0 : g 0 = ricciTau 2 := by simp [g, ricciTau]
  have hcont : ContinuousAt g 0 := by
    dsimp [g]
    fun_prop (disch := simpa using hd)
  have hnear : ∀ᶠ ε : ℝ in nhds 0, g ε < ricciTau 2 + η :=
    hcont.tendsto.eventually (eventually_lt_nhds (by rw [hg0]; linarith))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let ε := min (δ / 2) (1 / 8)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨ε, hε, lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  apply hball
  simpa [Real.dist_eq, abs_of_pos hε] using hεδ

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_support_geometric_sum (ε : ℝ) (hε : ε < 1 / 4) (n : ℕ) :
    let a : ℕ → ℝ := fun i => if i = 0 then exp (-0.90 / 2 + ε)
      else if i = 1 then exp (-1.46 / 2 + 2 * ε)
      else exp (-1.98 / 2 + 3 * ε) * exp (-0.50 / 2 + ε) ^ (i - 2)
    (∑ i ∈ range n, a i) ≤
      exp (-0.90 / 2 + ε) + exp (-1.46 / 2 + 2 * ε) +
        exp (-1.98 / 2 + 3 * ε) / (1 - exp (-0.50 / 2 + ε)) := by
  dsimp only
  let q := exp (-0.50 / 2 + ε)
  have hq0 : 0 ≤ q := (exp_pos _).le
  have hq1 : q < 1 := exp_lt_one_iff.mpr (by linarith)
  have hgeom (k : ℕ) : (∑ i ∈ range k, q ^ i) ≤ 1 / (1 - q) := by
    have hsum := (hasSum_geometric_of_lt_one hq0 hq1).summable.sum_le_tsum
      (range k) (fun i _ => pow_nonneg hq0 i)
    simpa only [(hasSum_geometric_of_lt_one hq0 hq1).tsum_eq, one_div] using hsum
  rcases n with _ | n
  · simp only [range_zero, sum_empty]
    positivity
  rcases n with _ | n
  · simp only [Nat.zero_add, range_one, sum_singleton]
    have hd : 0 < 1 - q := sub_pos.mpr hq1
    change exp (-0.90 / 2 + ε) ≤ exp (-0.90 / 2 + ε) +
      exp (-1.46 / 2 + 2 * ε) + exp (-1.98 / 2 + 3 * ε) / (1 - q)
    have hcdiv : 0 ≤ exp (-1.98 / 2 + 3 * ε) / (1 - q) :=
      div_nonneg (exp_pos _).le hd.le
    linarith [exp_pos (-1.46 / 2 + 2 * ε)]
  · rw [show n + 1 + 1 = 2 + n by omega, sum_range_add]
    have hhead : (∑ i ∈ range 2, if i = 0 then exp (-0.90 / 2 + ε)
        else if i = 1 then exp (-1.46 / 2 + 2 * ε)
        else exp (-1.98 / 2 + 3 * ε) * exp (-0.50 / 2 + ε) ^ (i - 2)) =
          exp (-0.90 / 2 + ε) + exp (-1.46 / 2 + 2 * ε) := by
      norm_num [sum_range_succ]
    rw [hhead]
    have htail : (∑ i ∈ range n,
        if 2 + i = 0 then exp (-0.90 / 2 + ε)
        else if 2 + i = 1 then exp (-1.46 / 2 + 2 * ε)
        else exp (-1.98 / 2 + 3 * ε) * q ^ (2 + i - 2)) =
          exp (-1.98 / 2 + 3 * ε) * ∑ i ∈ range n, q ^ i := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      have h1 : 2 + i ≠ 1 := by omega
      simp [h1, show 2 + i - 2 = i by omega]
    change _ ≤ exp (-0.90 / 2 + ε) + exp (-1.46 / 2 + 2 * ε) +
      exp (-1.98 / 2 + 3 * ε) / (1 - q)
    rw [htail]
    have hh := mul_le_mul_of_nonneg_left (hgeom n) (exp_pos (-1.98 / 2 + 3 * ε)).le
    simpa only [mul_one_div, add_comm] using add_le_add_left hh
      (exp (-0.90 / 2 + ε) + exp (-1.46 / 2 + 2 * ε))

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_three_blocks_head_positive (h : ℕ → ℕ) :
    ∃ a b c w : ℕ → ℕ,
      (∀ n, c n ≤ b n ∧ b n ≤ a n ∧ a n ≤ w n) ∧ Tendsto c atTop atTop ∧
      Tendsto (fun n => ∑ i ∈ range 2, ∑ j ∈ range 4, ∑ k ∈ range 6,
        if i + j ≤ 3 ∧ i + j + k ≤ 5 then
          (-1 : ℝ) ^ (i + j + k) *
            esymm (nuN (h n)) ((Ioc (a n) (w n)).filter Nat.Prime) i *
            esymm (nuN (h n)) ((Ioc (b n) (a n)).filter Nat.Prime) j *
            esymm (nuN (h n)) ((Ioc (c n) (b n)).filter Nat.Prime) k else 0)
        atTop (nhds (Ebar3 (90 / 100) (56 / 100) (52 / 100) : ℝ)) ∧
      ∀ᶠ n : ℕ in atTop, (0.0122847 : ℝ) <
        ∑ i ∈ range 2, ∑ j ∈ range 4, ∑ k ∈ range 6,
          if i + j ≤ 3 ∧ i + j + k ≤ 5 then
            (-1 : ℝ) ^ (i + j + k) *
              esymm (nuN (h n)) ((Ioc (a n) (w n)).filter Nat.Prime) i *
              esymm (nuN (h n)) ((Ioc (b n) (a n)).filter Nat.Prime) j *
              esymm (nuN (h n)) ((Ioc (c n) (b n)).filter Nat.Prime) k else 0 := by
  have hchoose (n : ℕ) : ∃ a b c w : ℕ, n + 2 < c ∧ c ≤ b ∧ b ≤ a ∧ a ≤ w ∧
      (0.90 - 1 / ((n : ℝ) + 1) < (∑ p ∈ (Ioc a w).filter Nat.Prime, nuN (h n) p) ∧
        (∑ p ∈ (Ioc a w).filter Nat.Prime, nuN (h n) p) ≤ 0.90) ∧
      (0.56 - 1 / ((n : ℝ) + 1) < (∑ p ∈ (Ioc b a).filter Nat.Prime, nuN (h n) p) ∧
        (∑ p ∈ (Ioc b a).filter Nat.Prime, nuN (h n) p) ≤ 0.56) ∧
      (0.52 - 1 / ((n : ℝ) + 1) < (∑ p ∈ (Ioc c b).filter Nat.Prime, nuN (h n) p) ∧
        (∑ p ∈ (Ioc c b).filter Nat.Prime, nuN (h n) p) ≤ 0.52) := by
    obtain ⟨W, _, hW⟩ := decompJ365_three_blocks_choose (1 / ((n : ℝ) + 1)) (by positivity) (n + 2)
    obtain ⟨a, b, c, hc, hcb, hba, haw, h₁, h₂, h₃, _⟩ := hW (h n) W le_rfl
    exact ⟨a, b, c, W, hc, hcb, hba, haw, h₁, h₂, h₃⟩
  choose a b c w hc using hchoose
  have hcdiv : Tendsto c atTop atTop :=
    tendsto_atTop_mono (fun n => (hc n).1.le) (tendsto_add_atTop_nat 2)
  have hbdiv : Tendsto b atTop atTop := tendsto_atTop_mono (fun n => (hc n).2.1) hcdiv
  have hadiv : Tendsto a atTop atTop := tendsto_atTop_mono (fun n => (hc n).2.2.1) hbdiv
  have heps : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hm₁ := fun n => (hc n).2.2.2.2.1
  have hm₂ := fun n => (hc n).2.2.2.2.2.1
  have hm₃ := fun n => (hc n).2.2.2.2.2.2
  have hmass (l u : ℕ → ℕ) (t : ℝ)
      (hm : ∀ n : ℕ, t - 1 / ((n : ℝ) + 1) <
          (∑ p ∈ (Ioc (l n) (u n)).filter Nat.Prime, nuN (h n) p) ∧
        (∑ p ∈ (Ioc (l n) (u n)).filter Nat.Prime, nuN (h n) p) ≤ t) :
      Tendsto (fun n => ∑ p ∈ (Ioc (l n) (u n)).filter Nat.Prime, nuN (h n) p)
        atTop (nhds t) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (by simpa using tendsto_const_nhds.sub heps) tendsto_const_nhds
    · intro n
      simpa only [one_div] using (hm n).1.le
    · exact fun n => (hm n).2
  have hsquare (l u : ℕ → ℕ) (t : ℝ) (hl : Tendsto l atTop atTop)
      (hl0 : ∀ n, 0 < l n)
      (hm : ∀ n, (∑ p ∈ (Ioc (l n) (u n)).filter Nat.Prime, nuN (h n) p) ≤ t) :
      Tendsto (fun n => ∑ p ∈ (Ioc (l n) (u n)).filter Nat.Prime, (nuN (h n) p) ^ 2)
        atTop (nhds 0) := by
    have hlR : Tendsto (fun n => (l n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hl
    have hbound : Tendsto (fun n => 2 / (l n : ℝ) * t) atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using ((tendsto_inv_atTop_zero.comp hlR).const_mul 2).mul_const t
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    · exact fun n => sum_nonneg (fun p _ => sq_nonneg _)
    · intro n
      exact (decompJ365_pair_block_square_upper (h n) (l n) (u n) (hl0 n)).trans
        (mul_le_mul_of_nonneg_left (hm n) (by positivity))
  have ha0 : ∀ n, 0 < a n := by intro n; have := hc n; omega
  have hb0 : ∀ n, 0 < b n := by intro n; have := hc n; omega
  have hc0 : ∀ n, 0 < c n := by intro n; have := hc n; omega
  have hH := decompJ365_lower_head_tendsto (fun n => nuN (h n))
    (fun n => (Ioc (a n) (w n)).filter Nat.Prime)
    (fun n => (Ioc (b n) (a n)).filter Nat.Prime)
    (fun n => (Ioc (c n) (b n)).filter Nat.Prime)
    (fun n => nuN_nonneg (h n)) (90 / 100) (56 / 100) (52 / 100)
    (by convert hmass a w 0.90 hm₁ using 1
        norm_num)
    (by convert hmass b a 0.56 hm₂ using 1
        norm_num)
    (by convert hmass c b 0.52 hm₃ using 1
        norm_num)
    (hsquare a w 0.90 hadiv ha0 (fun n => (hm₁ n).2))
    (hsquare b a 0.56 hbdiv hb0 (fun n => (hm₂ n).2))
    (hsquare c b 0.52 hcdiv hc0 (fun n => (hm₃ n).2))
  have hr : (0.0122847 : ℝ) < (Ebar3 (90 / 100) (56 / 100) (52 / 100) : ℝ) := by
    norm_num [Ebar3]
  exact ⟨a, b, c, w, fun n => ⟨(hc n).2.1, (hc n).2.2.1, (hc n).2.2.2.1⟩,
    hcdiv, hH, hH.eventually (eventually_gt_nhds hr)⟩

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_uncorrected_beta_certificate_negative :
    (Ebar3 (90 / 100) (56 / 100) (52 / 100) : ℝ) -
      (0.544 : ℝ) * (∑ k ∈ range 7, ricciBetaMajorant 0.4 (4 + k)) < 0 := by
  norm_num [Ebar3, ricciBetaMajorant, sum_range_succ, Nat.factorial]

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_uncorrected_beta_head_negative :
    (Ebar3 (90 / 100) (56 / 100) (52 / 100) : ℝ) -
      (0.90 * 0.56 ^ (2 : ℕ) * 0.52 ^ (2 : ℕ) /
        (0.50 ^ (5 : ℕ) * exp (3 * 0.50))) *
      (∑ k ∈ range 7, ricciBetaMajorant (exp (0.5 : ℝ) / 4) (4 + k)) < 0 := by
  let K : ℝ := 0.90 * 0.56 ^ (2 : ℕ) * 0.52 ^ (2 : ℕ) /
    (0.50 ^ (5 : ℕ) * exp (3 * 0.50))
  have hq : (0.4 : ℝ) ≤ exp 0.5 / 4 := by
    have hh : (1.6 : ℝ) ≤ exp 0.5 := ricci_exp_lower (by norm_num)
      (by norm_num [sum_range_succ, Nat.factorial])
    linarith
  have he075 : exp (0.75 : ℝ) ≤ 2.118 := ricci_exp_upper_small (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ, Nat.factorial])
  have he15 : exp (1.5 : ℝ) ≤ 4.486 := by
    rw [show (1.5 : ℝ) = 0.75 + 0.75 by norm_num, exp_add]
    nlinarith [exp_pos (0.75 : ℝ)]
  have hK : (0.544 : ℝ) ≤ K := by
    dsimp [K]
    rw [le_div_iff₀ (by positivity)]
    norm_num
    nlinarith
  have hsum : (∑ k ∈ range 7, ricciBetaMajorant 0.4 (4 + k)) ≤
      ∑ k ∈ range 7, ricciBetaMajorant (exp (0.5 : ℝ) / 4) (4 + k) := by
    apply sum_le_sum
    intro k hk
    unfold ricciBetaMajorant
    gcongr
  have hs0 : 0 ≤ ∑ k ∈ range 7, ricciBetaMajorant 0.4 (4 + k) := by
    apply sum_nonneg
    intro k hk
    unfold ricciBetaMajorant
    positivity
  have hprod := mul_le_mul hK hsum hs0 (by positivity : (0 : ℝ) ≤ K)
  have hbase := decompJ365_uncorrected_beta_certificate_negative
  change (Ebar3 (90 / 100) (56 / 100) (52 / 100) : ℝ) - K * _ < 0
  linarith

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_support_profile (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, ∃ α : ℕ → ℝ, 0 < ε ∧ ε < 1 / 4 ∧ α 0 = 1 ∧
      (∀ i, 0 < α i) ∧ (∀ i, α (i + 1) ≤ α i) ∧
      (∀ n, (∑ i ∈ range n, α (i + 1)) ≤ ricciTau 2 + η) ∧
      α 1 = exp (-0.90 / 2 + ε) ∧ α 2 = exp (-1.46 / 2 + 2 * ε) ∧
      ∀ i, α (i + 3) = exp (-1.98 / 2 + 3 * ε) * exp (-0.50 / 2 + ε) ^ i := by
  obtain ⟨ε, hε0, hε, hsum⟩ := decompJ365_tau_support_perturbation η hη
  let q := exp (-0.50 / 2 + ε)
  let α : ℕ → ℝ := fun i => if i = 0 then 1 else if i = 1 then exp (-0.90 / 2 + ε)
    else if i = 2 then exp (-1.46 / 2 + 2 * ε)
    else exp (-1.98 / 2 + 3 * ε) * q ^ (i - 3)
  have hq : q < 1 := exp_lt_one_iff.mpr (by linarith)
  have hq0 : 0 ≤ q := (exp_pos _).le
  have hpos (i : ℕ) : 0 < α i := by
    dsimp [α]
    split_ifs <;> positivity
  have hmono (i : ℕ) : α (i + 1) ≤ α i := by
    rcases i with _ | i
    · simpa [α] using exp_le_one_iff.mpr (show -0.90 / 2 + ε ≤ 0 by linarith)
    rcases i with _ | i
    · simp only [Nat.zero_add]
      change exp (-1.46 / 2 + 2 * ε) ≤ exp (-0.90 / 2 + ε)
      exact exp_le_exp.mpr (by linarith)
    rcases i with _ | i
    · change exp (-1.98 / 2 + 3 * ε) * q ^ 0 ≤ exp (-1.46 / 2 + 2 * ε)
      rw [pow_zero, mul_one]
      exact exp_le_exp.mpr (by linarith)
    · have hne0 : i + 1 + 1 + 1 ≠ 0 := by omega
      have hne1 : i + 1 + 1 + 1 ≠ 1 := by omega
      have hne2 : i + 1 + 1 + 1 ≠ 2 := by omega
      have hne0' : i + 1 + 1 + 1 + 1 ≠ 0 := by omega
      have hne1' : i + 1 + 1 + 1 + 1 ≠ 1 := by omega
      have hne2' : i + 1 + 1 + 1 + 1 ≠ 2 := by omega
      simp only [α, ite_eq_right hne0, ite_eq_right hne1, ite_eq_right hne2,
        ite_eq_right hne0', ite_eq_right hne1', ite_eq_right hne2']
      rw [show i + 1 + 1 + 1 - 3 = i by omega,
        show i + 1 + 1 + 1 + 1 - 3 = i + 1 by omega, pow_succ]
      nlinarith [mul_le_mul_of_nonneg_left hq.le
        (show 0 ≤ exp (-1.98 / 2 + 3 * ε) * q ^ i by positivity)]
  have hshift (i : ℕ) : α (i + 1) = if i = 0 then exp (-0.90 / 2 + ε)
      else if i = 1 then exp (-1.46 / 2 + 2 * ε)
      else exp (-1.98 / 2 + 3 * ε) * q ^ (i - 2) := by
    by_cases hi0 : i = 0
    · subst i
      norm_num [α]
    by_cases hi1 : i = 1
    · subst i
      norm_num [α]
    have h2 : i + 1 ≠ 2 := by omega
    simp [α, hi0, hi1, h2, show i + 1 - 3 = i - 2 by omega]
  refine ⟨ε, α, hε0, hε, by simp [α], hpos, hmono, ?_, by simp [α], by simp [α], ?_⟩
  · intro n
    simp_rw [hshift]
    exact (decompJ365_support_geometric_sum ε hε n).trans hsum.le
  · intro i
    have h1 : i + 3 ≠ 1 := by omega
    have h2 : i + 3 ≠ 2 := by omega
    simp [α, h1, h2, show i + 3 - 3 = i by omega, q]

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_beta_bar_four_coefficient :
    (∑ i ∈ range 2, ∑ j ∈ range 4, ∑ k ∈ range 6,
      if i + j ≤ 3 ∧ i + j + k ≤ 5 then
        (1 : ℚ) / ((i.factorial : ℚ) * j.factorial * k.factorial * (8 - i - j - k).factorial)
      else 0) = 1783 / 8064 ∧ (1783 / 8064 : ℚ) ≤ 979 / 4032 := by
  norm_num [sum_range_succ, Nat.factorial]

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_beta_bar_four_printed :
    (∑ i ∈ range 2, ∑ j ∈ range 4, ∑ k ∈ range 6,
      if i + j ≤ 3 ∧ i + j + k ≤ 5 then
        ((90 / 100 : ℚ) ^ i / (i.factorial : ℚ)) *
        ((56 / 100 : ℚ) ^ j / (j.factorial : ℚ)) *
        ((52 / 100 : ℚ) ^ k / (k.factorial : ℚ)) *
        ((50 / 100 : ℚ) ^ (8 - i - j - k) / ((8 - i - j - k).factorial : ℚ))
      else 0) ≤
      (90 / 100 : ℚ) * (56 / 100 : ℚ) ^ 2 * (52 / 100 : ℚ) ^ 2 * (50 / 100 : ℚ) ^ 3 *
        (979 / 4032 : ℚ) := by
  norm_num [sum_range_succ, Nat.factorial]

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_first_case_support_parameters :
    ∃ ε : ℝ, ∃ α : ℕ → ℝ, ∃ δ κ : ℝ,
      0 < ε ∧ ε < 1 / 4 ∧ 0 < δ ∧ 0 < κ ∧ 1 / 7 < δ ∧
      α 1 = exp (-0.90 / 2 + ε) ∧ α 2 = exp (-1.46 / 2 + 2 * ε) ∧
      (∀ i, α (i + 3) = exp (-1.98 / 2 + 3 * ε) * exp (-0.50 / 2 + ε) ^ i) ∧
      ∀ (n : ℕ) (S : Finset ℕ) (N T : ℝ), 1 ≤ N → 1 < T → T ≤ N ^ δ →
        (∀ p ∈ S, 0 < p) → (∀ p ∈ S, (p : ℝ) ≤ T) → S.card ≤ 2 * n + 1 →
        (∀ i ∈ range n,
          (S.filter (fun p : ℕ => T ^ (α (i + 1)) < (p : ℝ))).card ≤ 2 * i + 1) →
        ((∏ p ∈ S, p : ℕ) : ℝ) ≤ N ^ (1 - κ) := by
  obtain ⟨ε, α, hε0, hε, hα0, hpos, hmono, hsum, hα1, hα2, htail⟩ :=
    decompJ365_support_profile 0.001 (by norm_num)
  have hm := decompJ365_first_four_saved_exponents
  dsimp only at hm
  obtain ⟨δ, κ, hδ, hκ, hδ7, _, hsave⟩ := hm.1
  refine ⟨ε, α, δ, κ, hε0, hε, hδ, hκ, hδ7, hα1, hα2, htail, ?_⟩
  intro n S N T hN hT hTN hp hmax hc hcap
  have hτ : 0 ≤ ricciTau 2 + 0.001 := by simpa using hsum 0
  apply decompJ365_nested_saved_support S N T δ (ricciTau 2 + 0.001) κ hN hT hTN hτ hκ
    α hmono hα0 n (hpos n).le (hsum n) hp hmax hc hcap
  convert hsave using 1 <;> ring

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_boundary_monomial (t₁ t₂ t₃ t : ℝ) (ht : 0 < t)
    (ht₃ : t ≤ t₃) (ht₂ : t₃ ≤ t₂) (ht₁ : t₂ ≤ t₁)
    (i j k l b : ℕ) (hb : 3 ≤ b) (hi : i ≤ 1) (hij : i + j ≤ 3)
    (hijk : i + j + k ≤ 5) (hs : i + j + k + l = 2 * b) :
    t₁ ^ i * t₂ ^ j * t₃ ^ k * t ^ l ≤ t₁ * t₂ ^ 2 * t₃ ^ 2 * t ^ (2 * b - 5) := by
  have ht₃0 : 0 < t₃ := ht.trans_le ht₃
  have ht₂0 : 0 < t₂ := ht₃0.trans_le ht₂
  have ht₁0 : 0 < t₁ := ht₂0.trans_le ht₁
  have hlog₁ : 0 ≤ log t₁ - log t₂ := sub_nonneg.mpr (log_le_log ht₂0 ht₁)
  have hlog₂ : 0 ≤ log t₂ - log t₃ := sub_nonneg.mpr (log_le_log ht₃0 ht₂)
  have hlog₃ : 0 ≤ log t₃ - log t := sub_nonneg.mpr (log_le_log ht ht₃)
  have hiR : (i : ℝ) ≤ 1 := by exact_mod_cast hi
  have hijR : (i : ℝ) + j ≤ 3 := by exact_mod_cast hij
  have hijkR : (i : ℝ) + j + k ≤ 5 := by exact_mod_cast hijk
  have hsR : (i : ℝ) + j + k + l = 2 * b := by exact_mod_cast hs
  have hsub : ((2 * b - 5 : ℕ) : ℝ) = 2 * (b : ℝ) - 5 := by
    rw [Nat.cast_sub (by omega : 5 ≤ 2 * b)]
    push_cast
    ring
  apply (log_le_log_iff (by positivity) (by positivity)).mp
  rw [log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity),
    log_mul (by positivity) (by positivity), log_mul (by positivity) (by positivity)]
  simp only [log_pow, hsub, Nat.cast_ofNat]
  have hbalance := congrArg (fun z : ℝ => z * log t) hsR
  nlinarith [mul_nonneg (sub_nonneg.mpr hiR) hlog₁,
    mul_nonneg (sub_nonneg.mpr hijR) hlog₂,
    mul_nonneg (sub_nonneg.mpr hijkR) hlog₃]

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_beta_boundary_bound (J : Finset (ℕ × ℕ × ℕ × ℕ))
    (t₁ t₂ t₃ t : ℝ) (ht : 0 < t) (ht₃ : t ≤ t₃) (ht₂ : t₃ ≤ t₂) (ht₁ : t₂ ≤ t₁)
    (b : ℕ) (hb : 3 ≤ b)
    (hJ : ∀ q ∈ J, q.1 ≤ 1 ∧ q.1 + q.2.1 ≤ 3 ∧ q.1 + q.2.1 + q.2.2.1 ≤ 5 ∧
      q.1 + q.2.1 + q.2.2.1 + q.2.2.2 = 2 * b) :
    (∑ q ∈ J, (t₁ ^ q.1 / (q.1.factorial : ℝ)) *
      (t₂ ^ q.2.1 / (q.2.1.factorial : ℝ)) *
      (t₃ ^ q.2.2.1 / (q.2.2.1.factorial : ℝ)) *
      (t ^ q.2.2.2 / (q.2.2.2.factorial : ℝ))) ≤
      t₁ * t₂ ^ 2 * t₃ ^ 2 * t ^ (2 * b - 5) *
        ∑ q ∈ J, 1 / ((q.1.factorial : ℝ) * q.2.1.factorial *
          q.2.2.1.factorial * q.2.2.2.factorial) := by
  rw [mul_sum]
  apply sum_le_sum
  intro q hq
  obtain ⟨hi, hij, hijk, hs⟩ := hJ q hq
  have hm := decompJ365_boundary_monomial t₁ t₂ t₃ t ht ht₃ ht₂ ht₁
    q.1 q.2.1 q.2.2.1 q.2.2.2 b hb hi hij hijk hs
  have hd : (0 : ℝ) ≤ (q.1.factorial : ℝ) * q.2.1.factorial *
      q.2.2.1.factorial * q.2.2.2.factorial := by positivity
  have hh := div_le_div_of_nonneg_right hm hd
  convert hh using 1 <;> ring

/-- Auxiliary step for the decreasing sieve.
The exact source scope and concrete instance are recorded in STATEMENTS.md. -/
lemma decompJ365_normalized_lower_iteration (E v Φ : ℕ → ℝ)
    (hv : ∀ i, 0 < v i) (hstep : ∀ i, v i * E i - Φ i ≤ E (i + 1)) (n : ℕ) :
    E 0 - (∑ i ∈ range n, Φ i / (∏ j ∈ range (i + 1), v j)) ≤
      E n / (∏ j ∈ range n, v j) := by
  have hp (k : ℕ) : 0 < ∏ j ∈ range k, v j := prod_pos (fun j _ => hv j)
  induction n with
  | zero => simp
  | succ n ih =>
    have hs : E n / (∏ j ∈ range n, v j) - Φ n / (∏ j ∈ range (n + 1), v j) ≤
        E (n + 1) / (∏ j ∈ range (n + 1), v j) := by
      apply (le_div_iff₀ (hp (n + 1))).mpr
      rw [sub_mul, div_mul_cancel₀ _ (hp (n + 1)).ne']
      have heq : (E n / (∏ j ∈ range n, v j)) * (∏ j ∈ range (n + 1), v j) =
          v n * E n := by
        rw [prod_range_succ]
        field_simp [(hp n).ne']
      rw [heq]
      exact hstep n
    calc
      _ = (E 0 - (∑ i ∈ range n, Φ i / (∏ j ∈ range (i + 1), v j))) -
          Φ n / (∏ j ∈ range (n + 1), v j) := by rw [sum_range_succ]; ring
      _ ≤ E n / (∏ j ∈ range n, v j) - Φ n / (∏ j ∈ range (n + 1), v j) :=
        sub_le_sub_right ih _
      _ ≤ _ := hs

open LeanLab.PNTSieve.Bonferroni

lemma decomp305_pair_decreasing_lower (h N : ℕ) (P J : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (cutoff level : ℕ → ℕ)
    (L : ℝ) (hL : 1 ≤ L)
    (hlevel : ∀ S ⊆ P, (∀ j ∈ J,
      (S.filter (fun p => cutoff j < p)).card ≤ 2 * level j + 1) →
        ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L) :
    let U := P.powerset.filter (fun S => ∀ j ∈ J,
      (S.filter (fun p => cutoff j < p)).card ≤ 2 * level j + 1)
    (N : ℝ) * (∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p) -
      L * (1 + Real.log L) ^ 2 ≤
      #{i ∈ range N | ∀ p ∈ P, ¬ p ∣ i * (i + h)} := by
  apply decompJ365_decreasing_lower_explicit (range N) P J
    (fun i => i * (i + h)) hP cutoff level h N (nuN h) ?_ L hL hlevel
  intro S hS
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => hP p (hS hp)
  have hd : 0 < ∏ p ∈ S, p := prod_pos (fun p hp => (hprime p hp).pos)
  have hdensity : (cnt h (∏ p ∈ S, p) : ℝ) / (∏ p ∈ S, p) =
      ∏ p ∈ S, nuN h p := by
    rw [cnt_prod_primes h S hprime, Nat.cast_prod, ← prod_div_distrib]
    exact prod_congr rfl (fun p hp => (nuN_prime (hprime p hp)).symm)
  have hmain : (N : ℝ) * (∏ p ∈ S, nuN h p) =
      (cnt h (∏ p ∈ S, p) : ℝ) * N / (∏ p ∈ S, p) := by
    rw [← hdensity]
    ring
  rw [hmain]
  exact decompJ365_pair_periodic_remainder h N (∏ p ∈ S, p) hd

lemma decomp305_pair_survivors_le_zCount (a b ξ N t : ℕ) (m : ℤ)
    (ht : 2 ≤ t) (hN : N + 2 * m.natAbs ≤ ξ + 1)
    (hsizeA : (ξ : ℝ) < (t : ℝ) ^ (a + 1))
    (hsizeB : (ξ : ℝ) < (t : ℝ) ^ (b + 1))
    (hthA : (ξ : ℝ) ^ (1 / ((a : ℝ) + 1)) ≤ t)
    (hthB : (ξ : ℝ) ^ (1 / ((b : ℝ) + 1)) ≤ t) :
    #{y ∈ range N | ∀ p ∈ Nat.primesLE t, ¬ p ∣ y * (y + 2 * m.natAbs)} ≤
      zCount a b m ξ := by
  let h := 2 * m.natAbs
  let f : ℕ → ℕ := fun y => if 0 ≤ m then y else y + h
  have hgap : (h : ℤ) = 2 * |m| := by simp [h, Int.natCast_natAbs]
  have hvalues (y : ℕ) :
      (f y : ℤ) + 2 * m = if 0 ≤ m then (y + h : ℕ) else y := by
    dsimp [f]
    split_ifs with hm
    · rw [abs_of_nonneg hm] at hgap
      push_cast
      omega
    · rw [abs_of_neg (lt_of_not_ge hm)] at hgap
      push_cast
      omega
  apply Finset.card_le_card_of_injOn f
  · intro y hy
    obtain ⟨hyN, hsieve⟩ := mem_filter.mp hy
    have hylt := mem_range.mp hyN
    have hy0 : 0 < y := by
      by_contra hy
      have hz : y = 0 := by omega
      have htwo : 2 ∈ Nat.primesLE t := Nat.mem_primesLE.mpr ⟨ht, Nat.prime_two⟩
      exact hsieve 2 htwo (by simp [hz])
    have hyξ : y + h ≤ ξ := by dsimp [h]; omega
    have hx1 : 1 ≤ f y := by dsimp [f]; split_ifs <;> omega
    have hxξ : f y ≤ ξ := by dsimp [f]; split_ifs <;> omega
    have hbpos : 0 < (f y : ℤ) + 2 * m := by
      rw [hvalues]
      split_ifs <;> positivity
    have hrough (z : ℕ) (hz : z = y ∨ z = y + h) :
        ∀ p ∈ z.primeFactorsList, (t : ℝ) < p := by
      intro p hp
      have hz0 : z ≠ 0 := by rcases hz with rfl | rfl <;> omega
      obtain ⟨hpprime, hpdvd⟩ := (Nat.mem_primeFactorsList hz0).mp hp
      by_contra htp
      have hpt : p ≤ t := by exact_mod_cast (le_of_not_gt htp : (p : ℝ) ≤ t)
      have hpP := Nat.mem_primesLE.mpr ⟨hpt, hpprime⟩
      apply hsieve p hpP
      rcases hz with rfl | rfl
      · exact dvd_mul_of_dvd_left hpdvd _
      · exact dvd_mul_of_dvd_right hpdvd _
    have hfy : f y = y ∨ f y = y + h := by dsimp [f]; split_ifs <;> simp
    have hbval : ((f y : ℤ) + 2 * m).toNat = if 0 ≤ m then y + h else y := by
      rw [hvalues]
      split_ifs <;> norm_cast
    have hb1 : 1 ≤ ((f y : ℤ) + 2 * m).toNat := by rw [hbval]; split_ifs <;> omega
    have hbξ : ((f y : ℤ) + 2 * m).toNat ≤ ξ := by rw [hbval]; split_ifs <;> omega
    have hbchoices : ((f y : ℤ) + 2 * m).toNat = y ∨
        ((f y : ℤ) + 2 * m).toNat = y + h := by rw [hbval]; split_ifs <;> simp
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (by omega : 1 ≤ t)
    have hA := almostGT_of_pow_bound hx1 ht1 (hrough (f y) hfy)
      ((by exact_mod_cast hxξ : (f y : ℝ) ≤ ξ).trans_lt hsizeA)
    have hB := almostGT_of_pow_bound hb1 ht1 (hrough _ hbchoices)
      ((by exact_mod_cast hbξ : (((f y : ℤ) + 2 * m).toNat : ℝ) ≤ ξ).trans_lt hsizeB)
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨hx1, hxξ⟩, almostGT_mono hA le_rfl ?_, hbpos,
      almostGT_mono hB le_rfl ?_⟩
    · exact (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hxξ)
        (by positivity)).trans hthA
    · exact (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hxξ)
        (by positivity)).trans hthB
  · intro y _ z _ heq
    dsimp [f] at heq
    split_ifs at heq <;> omega


/-- Second memoir page 98 formula 16.2, before the next cardinality truncation.
Adjoining a disjoint block multiplies the retained signed main sum by its density product. -/

lemma decomp305_block_extension (x : ℕ → ℝ) (P B : Finset ℕ) (hPB : Disjoint P B)
    (A : Finset ℕ → Prop) [DecidablePred A] :
    (∑ S ∈ (P ∪ B).powerset.filter (fun S => A (S ∩ P)),
      (-1 : ℝ) ^ S.card * ∏ p ∈ S, x p) =
      (∑ S ∈ P.powerset.filter A, (-1 : ℝ) ^ S.card * ∏ p ∈ S, x p) *
        ∏ p ∈ B, (1 - x p) := by
  induction B using Finset.induction_on with
  | empty =>
    simp only [union_empty, prod_empty, mul_one, sum_filter]
    apply sum_congr rfl
    intro S hS
    rw [inter_eq_left.mpr (mem_powerset.mp hS)]
  | @insert p B hp ih =>
    have hpP : p ∉ P := fun h => (Finset.disjoint_left.mp hPB) h (mem_insert_self p B)
    have hPB' : Disjoint P B := hPB.mono_right (subset_insert p B)
    have hpU : p ∉ P ∪ B := by simp [hpP, hp]
    have hU : P ∪ insert p B = insert p (P ∪ B) := by ext q; simp [or_left_comm, or_assoc, or_comm]
    rw [hU, sum_filter, sum_powerset_insert hpU]
    have hterm (S : Finset ℕ) (hS : S ∈ (P ∪ B).powerset) :
        (if A (insert p S ∩ P) then
          (-1 : ℝ) ^ (insert p S).card * ∏ q ∈ insert p S, x q else 0) =
        -x p * (if A (S ∩ P) then (-1 : ℝ) ^ S.card * ∏ q ∈ S, x q else 0) := by
      have hpS : p ∉ S := fun h => hpU (mem_powerset.mp hS h)
      have hint : insert p S ∩ P = S ∩ P := by ext q; simp only [mem_inter, mem_insert]; aesop
      rw [hint, card_insert_of_notMem hpS, prod_insert hpS, pow_succ]
      split_ifs <;> ring
    rw [sum_congr rfl hterm, ← mul_sum, ← sum_filter, ih hPB', prod_insert hp]
    ring


/-- Second memoir page 98 formula 15.6, auxiliary disjoint block expansion.
Every subset has a unique old part and a unique new part. -/

lemma decomp305_disjoint_powerset_sum (P B : Finset ℕ) (hPB : Disjoint P B)
    (g : Finset ℕ → ℝ) :
    (∑ V ∈ (P ∪ B).powerset, g V) =
      ∑ S ∈ P.powerset, ∑ T ∈ B.powerset, g (S ∪ T) := by
  have hparts (S T : Finset ℕ) (hS : S ⊆ P) (hT : T ⊆ B) :
      (S ∪ T) ∩ P = S ∧ (S ∪ T) ∩ B = T := by
    have hd : ∀ q ∈ P, q ∉ B := fun q hq hb => Finset.disjoint_left.mp hPB hq hb
    constructor <;> ext q <;> simp only [mem_inter, mem_union]
    · constructor
      · rintro ⟨hq | hq, hqP⟩
        · exact hq
        · exact False.elim (hd q hqP (hT hq))
      · intro hq; exact ⟨Or.inl hq, hS hq⟩
    · constructor
      · rintro ⟨hq | hq, hqB⟩
        · exact False.elim (hd q (hS hq) hqB)
        · exact hq
      · intro hq; exact ⟨Or.inr hq, hT hq⟩
  rw [← sum_product P.powerset B.powerset (fun ST => g (ST.1 ∪ ST.2))]
  symm
  apply sum_bij (fun ST _ => ST.1 ∪ ST.2)
  · intro ST hST
    obtain ⟨hS, hT⟩ := mem_product.mp hST
    exact mem_powerset.mpr (union_subset_union (mem_powerset.mp hS) (mem_powerset.mp hT))
  · intro ST hST UV hUV heq
    obtain ⟨hS, hT⟩ := mem_product.mp hST
    obtain ⟨hU, hV⟩ := mem_product.mp hUV
    obtain ⟨hSP, hTB⟩ := hparts ST.1 ST.2 (mem_powerset.mp hS) (mem_powerset.mp hT)
    obtain ⟨hUP, hVB⟩ := hparts UV.1 UV.2 (mem_powerset.mp hU) (mem_powerset.mp hV)
    apply Prod.ext
    · rw [← hSP, ← hUP, heq]
    · rw [← hTB, ← hVB, heq]
  · intro V hV
    refine ⟨(V ∩ P, V ∩ B), mem_product.mpr ⟨mem_powerset.mpr inter_subset_right,
      mem_powerset.mpr inter_subset_right⟩, ?_⟩
    have hv := mem_powerset.mp hV
    ext q
    simp only [mem_union, mem_inter]
    constructor
    · tauto
    · intro hq
      rcases mem_union.mp (hv hq) with hP | hB
      · exact Or.inl ⟨hq, hP⟩
      · exact Or.inr ⟨hq, hB⟩
  · intro ST hST
    rfl



/-- Second memoir page 98 formula 15.6 with the lower cardinality cutoff.
This identifies the actual retained family with its block convolution. -/

lemma decomp305_retained_block_expansion (x : ℕ → ℝ) (P B : Finset ℕ)
    (hPB : Disjoint P B) (A : Finset ℕ → Prop) [DecidablePred A] (r : ℕ)
    (hcard : ∀ S ⊆ P, A S → S.card ≤ r) :
    (∑ V ∈ (P ∪ B).powerset.filter (fun V => A (V ∩ P) ∧ V.card ≤ r),
      (-1 : ℝ) ^ V.card * ∏ p ∈ V, x p) =
      ∑ S ∈ P.powerset.filter A, (-1 : ℝ) ^ S.card * (∏ p ∈ S, x p) *
        (∑ T ∈ B.powerset.filter (fun T => T.card ≤ r - S.card),
          (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p) := by
  rw [sum_filter, decomp305_disjoint_powerset_sum P B hPB, sum_filter]
  apply sum_congr rfl
  intro S hS
  have hSP : S ⊆ P := mem_powerset.mp hS
  by_cases hAS : A S
  · rw [if_pos hAS, mul_sum]
    rw [sum_filter]
    apply sum_congr rfl
    intro T hT
    have hTB : T ⊆ B := mem_powerset.mp hT
    have hST : Disjoint S T := hPB.mono hSP hTB
    have hTP : Disjoint T P := (hPB.mono_right hTB).symm
    have hint : (S ∪ T) ∩ P = S := by
      rw [union_inter_distrib_right, inter_eq_left.mpr hSP,
        disjoint_iff_inter_eq_empty.mp hTP, union_empty]
    rw [hint, card_union_of_disjoint hST, prod_union hST]
    have hc : S.card + T.card ≤ r ↔ T.card ≤ r - S.card := by
      have := hcard S hSP hAS
      omega
    simp only [hAS, true_and, hc, pow_add]
    split_ifs <;> ring
  · rw [if_neg hAS]
    apply sum_eq_zero
    intro T hT
    have hTB : T ⊆ B := mem_powerset.mp hT
    have hTP : Disjoint T P := (hPB.mono_right hTB).symm
    have hint : (S ∪ T) ∩ P = S := by
      rw [union_inter_distrib_right, inter_eq_left.mpr hSP,
        disjoint_iff_inter_eq_empty.mp hTP, union_empty]
    simp [hint, hAS]


/-- Second memoir page 99 formula 17.4, auxiliary lower recurrence.
The next truncation loses at most its first omitted unsigned coefficient. -/

lemma decomp305_truncated_block_lower (x : ℕ → ℝ)
    (hx0 : ∀ p, 0 ≤ x p)
    (U : Finset (Finset ℕ)) (B : Finset ℕ) (hx1 : ∀ p ∈ B, x p ≤ 1) (r : ℕ)
    (hcard : ∀ S ∈ U, S.card ≤ r) :
    (∏ p ∈ B, (1 - x p)) *
        (∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, x p) -
      (∑ S ∈ U, (∏ p ∈ S, x p) *
        LeanLab.PNTSieve.Bonferroni.esymm x B (r - S.card + 1)) ≤
      ∑ S ∈ U, (-1 : ℝ) ^ S.card * (∏ p ∈ S, x p) *
        (∑ T ∈ B.powerset.filter (fun T => T.card ≤ r - S.card),
          (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p) := by
  let y : ℕ → ℝ := fun p => if p ∈ B then x p else 0
  have hy0 : ∀ p, 0 ≤ y p := by
    intro p
    dsimp [y]
    split_ifs
    · exact hx0 p
    · norm_num
  have hy1 : ∀ p, y p ≤ 1 := by
    intro p
    dsimp [y]
    split_ifs with hp
    · exact hx1 p hp
    · norm_num
  have hprod (T : Finset ℕ) (hT : T ⊆ B) :
      (∏ p ∈ T, y p) = ∏ p ∈ T, x p :=
    prod_congr rfl (fun p hp => if_pos (hT hp))
  have hpi : (∏ p ∈ B, (1 - y p)) = ∏ p ∈ B, (1 - x p) :=
    prod_congr rfl (fun p hp => by simp only [y, if_pos hp])
  have hterm (S : Finset ℕ) (hS : S ∈ U) :
      |(∑ T ∈ B.powerset.filter (fun T => T.card ≤ r - S.card),
        (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p) - ∏ p ∈ B, (1 - x p)| ≤
      LeanLab.PNTSieve.Bonferroni.esymm x B (r - S.card + 1) := by
    have hd := LeanLab.PNTSieve.Bonferroni.weighted_dev y hy0 hy1 B (r - S.card)
    change _ ≤ LeanLab.PNTSieve.Bonferroni.esymm y B (r - S.card + 1) at hd
    rw [hpi] at hd
    have hs : (∑ T ∈ B.powerset.filter (fun T => T.card ≤ r - S.card),
        (-1 : ℝ) ^ T.card * ∏ p ∈ T, y p) =
        ∑ T ∈ B.powerset.filter (fun T => T.card ≤ r - S.card),
          (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p := by
      apply sum_congr rfl
      intro T hT
      rw [hprod T (mem_powerset.mp (mem_filter.mp hT).1)]
    have he : LeanLab.PNTSieve.Bonferroni.esymm y B (r - S.card + 1) =
        LeanLab.PNTSieve.Bonferroni.esymm x B (r - S.card + 1) := by
      unfold LeanLab.PNTSieve.Bonferroni.esymm
      exact sum_congr rfl (fun T hT => hprod T (mem_powersetCard.mp hT).1)
    rwa [hs, he] at hd
  have hbound (S : Finset ℕ) (hS : S ∈ U) :
      (∏ p ∈ B, (1 - x p)) * ((-1 : ℝ) ^ S.card * ∏ p ∈ S, x p) -
        (∏ p ∈ S, x p) * LeanLab.PNTSieve.Bonferroni.esymm x B (r - S.card + 1) ≤
      (-1 : ℝ) ^ S.card * (∏ p ∈ S, x p) *
        (∑ T ∈ B.powerset.filter (fun T => T.card ≤ r - S.card),
          (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p) := by
    have hdev := hterm S hS
    have hwt : 0 ≤ ∏ p ∈ S, x p := prod_nonneg (fun p _ => hx0 p)
    have habs := mul_le_mul_of_nonneg_left hdev hwt
    have hsgn : |(-1 : ℝ) ^ S.card| = 1 := by simp
    have hmin := neg_abs_le ((-1 : ℝ) ^ S.card *
      ((∑ T ∈ B.powerset.filter (fun T => T.card ≤ r - S.card),
        (-1 : ℝ) ^ T.card * ∏ p ∈ T, x p) - ∏ p ∈ B, (1 - x p)))
    rw [abs_mul, hsgn, one_mul] at hmin
    have hmul := mul_le_mul_of_nonneg_left hmin hwt
    change (∏ p ∈ S, x p) * |(_ : ℝ)| ≤
      (∏ p ∈ S, x p) * LeanLab.PNTSieve.Bonferroni.esymm x B (r - S.card + 1) at habs
    nlinarith
  have hh := sum_le_sum hbound
  simpa only [sum_sub_distrib, ← mul_sum] using hh


/-- Second memoir page 99 formula 17.4 for an actual retained subset family.
The boundary is the unsigned convolution coefficient at the first omitted degree. -/

lemma decomp305_retained_step_lower (x : ℕ → ℝ)
    (hx0 : ∀ p, 0 ≤ x p)
    (P B : Finset ℕ) (hPB : Disjoint P B) (hx1 : ∀ p ∈ B, x p ≤ 1)
    (A : Finset ℕ → Prop) [DecidablePred A] (r : ℕ)
    (hcard : ∀ S ⊆ P, A S → S.card ≤ r) :
    (∏ p ∈ B, (1 - x p)) *
        (∑ S ∈ P.powerset.filter A, (-1 : ℝ) ^ S.card * ∏ p ∈ S, x p) -
      (∑ S ∈ P.powerset.filter A, (∏ p ∈ S, x p) *
        LeanLab.PNTSieve.Bonferroni.esymm x B (r - S.card + 1)) ≤
      ∑ V ∈ (P ∪ B).powerset.filter (fun V => A (V ∩ P) ∧ V.card ≤ r),
        (-1 : ℝ) ^ V.card * ∏ p ∈ V, x p := by
  rw [decomp305_retained_block_expansion x P B hPB A r hcard]
  exact decomp305_truncated_block_lower x hx0 (P.powerset.filter A) B hx1 r
    (fun S hS => hcard S (mem_powerset.mp (mem_filter.mp hS).1) (mem_filter.mp hS).2)


/-- Second memoir pages 92, 93 and 106.
The actual nested odd cap family on primes between the current cutoff and w. -/

private def decomp305PrimeFamily (w : ℕ) (c : ℕ → ℕ) (n : ℕ) : Finset (Finset ℕ) :=
  ((Ioc (c n) w).filter Nat.Prime).powerset.filter (fun S =>
    ∀ j ∈ range (n + 1), (S.filter (fun p => c j < p)).card ≤ 2 * j + 1)


/-- Second memoir page 97 formula 14.8, the last cap bounds the whole retained set. -/

lemma decomp305_prime_family_card (w : ℕ) (c : ℕ → ℕ) (n : ℕ)
    (S : Finset ℕ) (hS : S ∈ decomp305PrimeFamily w c n) : S.card ≤ 2 * n + 1 := by
  simp only [decomp305PrimeFamily, mem_filter, mem_powerset] at hS
  obtain ⟨hSP, hcaps⟩ := hS
  have hfilter : S.filter (fun p => c n < p) = S := by
    apply filter_eq_self.mpr
    intro p hp
    exact (mem_Ioc.mp (mem_filter.mp (hSP hp)).1).1
  simpa only [hfilter] using hcaps n (mem_range.mpr (by omega))


/-- Second memoir pages 97 and 98 formulas 15.6 and 16.2.
The next actual prime family is obtained by adjoining the next block and imposing its odd cap. -/

lemma decomp305_prime_family_step (w : ℕ) (c : ℕ → ℕ) (hc : Antitone c)
    (n : ℕ) (hw : c n ≤ w) :
    decomp305PrimeFamily w c (n + 1) =
      (((Ioc (c n) w).filter Nat.Prime) ∪
        ((Ioc (c (n + 1)) (c n)).filter Nat.Prime)).powerset.filter
        (fun V => (V ∩ ((Ioc (c n) w).filter Nat.Prime)) ∈ decomp305PrimeFamily w c n ∧
          V.card ≤ 2 * (n + 1) + 1) := by
  let P := (Ioc (c n) w).filter Nat.Prime
  let Q := (Ioc (c (n + 1)) w).filter Nat.Prime
  have hPsub : P ⊆ Q := by
    intro p hp
    obtain ⟨hpI, hpprime⟩ := mem_filter.mp hp
    obtain ⟨hpl, hpu⟩ := mem_Ioc.mp hpI
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(hc (by omega : n ≤ n + 1)).trans_lt hpl, hpu⟩, hpprime⟩
  have hPQ : P ∪ ((Ioc (c (n + 1)) (c n)).filter Nat.Prime) = Q := by
    ext p
    simp only [P, Q, mem_union, mem_filter, mem_Ioc]
    have hcn := hc (by omega : n ≤ n + 1)
    by_cases hp : p.Prime
    · simp only [hp, and_true]
      omega
    · simp [hp]
  rw [hPQ]
  ext V
  simp only [decomp305PrimeFamily, mem_filter, mem_powerset]
  have hfilters (hV : V ⊆ Q) (j : ℕ) (hj : j ≤ n) :
      (V ∩ P).filter (fun p => c j < p) = V.filter (fun p => c j < p) := by
    ext p
    simp only [mem_filter, mem_inter]
    constructor
    · tauto
    · rintro ⟨hpV, hpj⟩
      have hpQ := mem_filter.mp (hV hpV)
      have hcn : c n ≤ c j := hc hj
      refine ⟨⟨hpV, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hcn.trans_lt hpj,
        (mem_Ioc.mp hpQ.1).2⟩, hpQ.2⟩⟩, hpj⟩
  constructor
  · rintro ⟨hV, hcaps⟩
    refine ⟨hV, ⟨inter_subset_right, ?_⟩, ?_⟩
    · intro j hj
      rw [hfilters hV j (by have := mem_range.mp hj; omega)]
      exact hcaps j (mem_range.mpr (by have := mem_range.mp hj; omega))
    · have hlast : V.filter (fun p => c (n + 1) < p) = V := by
        apply filter_eq_self.mpr
        intro p hp
        exact (mem_Ioc.mp (mem_filter.mp (hV hp)).1).1
      simpa only [hlast] using hcaps (n + 1) (mem_range.mpr (by omega))
  · rintro ⟨hV, ⟨_, hcaps⟩, hcard⟩
    refine ⟨hV, ?_⟩
    intro j hj
    have hjn := mem_range.mp hj
    by_cases hje : j = n + 1
    · subst j
      exact (card_filter_le _ _).trans hcard
    · rw [← hfilters hV j (by omega)]
      exact hcaps j (mem_range.mpr (by omega))


/-- Second memoir page 99 formula 17.4 with the actual prime blocks and pair densities.
The boundary coefficient is explicit. No positive main estimate is assumed. -/

lemma decomp305_pair_prime_recurrence (h w : ℕ) (heven : Even h)
    (c : ℕ → ℕ) (hc : Antitone c) (n : ℕ) (hw : c n ≤ w) :
    let B := (Ioc (c (n + 1)) (c n)).filter Nat.Prime
    (∏ p ∈ B, (1 - nuN h p)) *
        (∑ S ∈ decomp305PrimeFamily w c n,
          (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p) -
      (∑ S ∈ decomp305PrimeFamily w c n, (∏ p ∈ S, nuN h p) *
        LeanLab.PNTSieve.Bonferroni.esymm (nuN h) B
          (2 * (n + 1) + 1 - S.card + 1)) ≤
      ∑ S ∈ decomp305PrimeFamily w c (n + 1),
        (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p := by
  let P := (Ioc (c n) w).filter Nat.Prime
  let B := (Ioc (c (n + 1)) (c n)).filter Nat.Prime
  have hPB : Disjoint P B := by
    apply disjoint_left.mpr
    intro p hpP hpB
    have hP := mem_Ioc.mp (mem_filter.mp hpP).1
    have hB := mem_Ioc.mp (mem_filter.mp hpB).1
    omega
  have hx1 : ∀ p ∈ B, nuN h p ≤ 1 := fun p hp =>
    (nuN_lt_one heven (mem_filter.mp hp).2).le
  have hUeq : P.powerset.filter (fun S => S ∈ decomp305PrimeFamily w c n) =
      decomp305PrimeFamily w c n := by
    ext S
    simp only [mem_filter, mem_powerset]
    constructor
    · exact And.right
    · intro hS
      refine ⟨?_, hS⟩
      simp only [decomp305PrimeFamily, mem_filter, mem_powerset] at hS
      exact hS.1
  have hcard : ∀ S ⊆ P, S ∈ decomp305PrimeFamily w c n →
      S.card ≤ 2 * (n + 1) + 1 := by
    intro S _ hS
    have := decomp305_prime_family_card w c n S hS
    omega
  have hraw := decomp305_retained_step_lower (nuN h) (nuN_nonneg h) P B hPB hx1
    (fun S => S ∈ decomp305PrimeFamily w c n) (2 * (n + 1) + 1) hcard
  rw [hUeq, ← decomp305_prime_family_step w c hc n hw] at hraw
  exact hraw


/-- Second memoir page 99 formula 18.3 with actual prime blocks and pair densities.
This instantiates the normalized iteration with the retained family and its boundary. -/

lemma decomp305_pair_prime_normalized (h w : ℕ) (heven : Even h)
    (c : ℕ → ℕ) (hc : Antitone c) (hw : c 0 ≤ w) (s n : ℕ) :
    let B := fun i => (Ioc (c (s + i + 1)) (c (s + i))).filter Nat.Prime
    let v := fun i => ∏ p ∈ B i, (1 - nuN h p)
    let E := fun i => ∑ S ∈ decomp305PrimeFamily w c (s + i),
      (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p
    let Φ := fun i => ∑ S ∈ decomp305PrimeFamily w c (s + i), (∏ p ∈ S, nuN h p) *
      LeanLab.PNTSieve.Bonferroni.esymm (nuN h) (B i)
        (2 * (s + i + 1) + 1 - S.card + 1)
    E 0 - (∑ i ∈ range n, Φ i / (∏ j ∈ range (i + 1), v j)) ≤
      E n / (∏ j ∈ range n, v j) := by
  dsimp only
  apply decompJ365_normalized_lower_iteration
    (fun i => ∑ S ∈ decomp305PrimeFamily w c (s + i),
      (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p)
    (fun i => ∏ p ∈ (Ioc (c (s + i + 1)) (c (s + i))).filter Nat.Prime, (1 - nuN h p))
    (fun i => ∑ S ∈ decomp305PrimeFamily w c (s + i), (∏ p ∈ S, nuN h p) *
      LeanLab.PNTSieve.Bonferroni.esymm (nuN h)
        ((Ioc (c (s + i + 1)) (c (s + i))).filter Nat.Prime)
        (2 * (s + i + 1) + 1 - S.card + 1)) ?_ ?_ n
  · intro i
    apply prod_pos
    intro p hp
    exact sub_pos.mpr (nuN_lt_one heven (mem_filter.mp hp).2)
  · intro i
    exact decomp305_pair_prime_recurrence h w heven c hc (s + i) ((hc (Nat.zero_le (s + i))).trans hw)


/-- First memoir pages 88 and 89 and second memoir pages 106 and 107.
The finite decreasing pair sieve bounds the actual Z count for either shift sign. -/

lemma decomp305_zCount_finite_lower (a b ξ N t : ℕ) (m : ℤ)
    (ht : 2 ≤ t) (hN : N + 2 * m.natAbs ≤ ξ + 1)
    (hsizeA : (ξ : ℝ) < (t : ℝ) ^ (a + 1))
    (hsizeB : (ξ : ℝ) < (t : ℝ) ^ (b + 1))
    (hthA : (ξ : ℝ) ^ (1 / ((a : ℝ) + 1)) ≤ t)
    (hthB : (ξ : ℝ) ^ (1 / ((b : ℝ) + 1)) ≤ t)
    (J : Finset ℕ) (cutoff level : ℕ → ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hlevel : ∀ S ⊆ Nat.primesLE t, (∀ j ∈ J,
      (S.filter (fun p => cutoff j < p)).card ≤ 2 * level j + 1) →
        ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L) :
    let U := (Nat.primesLE t).powerset.filter (fun S => ∀ j ∈ J,
      (S.filter (fun p => cutoff j < p)).card ≤ 2 * level j + 1)
    (N : ℝ) * (∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN (2 * m.natAbs) p) -
      L * (1 + Real.log L) ^ 2 ≤ zCount a b m ξ := by
  apply (decomp305_pair_decreasing_lower (2 * m.natAbs) N (Nat.primesLE t) J
    (fun p hp => (Nat.mem_primesLE.mp hp).2) cutoff level L hL hlevel).trans
  exact_mod_cast decomp305_pair_survivors_le_zCount a b ξ N t m ht hN
    hsizeA hsizeB hthA hthB


/-- First memoir pages 88 and 89 and second memoir pages 106 and 107.
The finite decreasing sieve bounds the actual W count at a common prime cutoff. -/

lemma decomp305_wCount_finite_lower (a b N t : ℕ) (ht : 2 ≤ t)
    (hthA : (N : ℝ) ^ (1 / ((a : ℝ) + 1)) ≤ t)
    (hthB : (N : ℝ) ^ (1 / ((b : ℝ) + 1)) ≤ t)
    (J : Finset ℕ) (cutoff level : ℕ → ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hlevel : ∀ S ⊆ Nat.primesLE t, (∀ j ∈ J,
      (S.filter (fun p => cutoff j < p)).card ≤ 2 * level j + 1) →
        ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L) :
    let U := (Nat.primesLE t).powerset.filter (fun S => ∀ j ∈ J,
      (S.filter (fun p => cutoff j < p)).card ≤ 2 * level j + 1)
    (N : ℝ) * (∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN N p) -
      L * (1 + Real.log L) ^ 2 ≤ wCount a b N := by
  have hP : ∀ p ∈ Nat.primesLE t, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  have herror (S : Finset ℕ) (hS : S ⊆ Nat.primesLE t) :
      |(#{i ∈ range N | (∏ p ∈ S, p) ∣ i * (N - i)} : ℝ) -
        (N : ℝ) * ∏ p ∈ S, nuN N p| ≤ cnt N (∏ p ∈ S, p) := by
    have hc := LeanLab.SchnirelmannGoldbach.PureSieve.multiples_error N S
      (fun p hp => hP p (hS hp))
    have hν : (∏ p ∈ S, (LeanLab.SchnirelmannGoldbach.S1.wt N p / p)) =
        ∏ p ∈ S, nuN N p :=
      prod_congr rfl (fun p hp => (nuN_prime (hP p (hS hp))).symm)
    rw [hν] at hc
    rw [cnt_prod_primes N S (fun p hp => hP p (hS hp))]
    simpa only [LeanLab.SchnirelmannGoldbach.PureSieve.multiples] using hc
  have hraw := decompJ365_decreasing_lower_explicit (range N) (Nat.primesLE t) J
    (fun i => i * (N - i)) hP cutoff level N N (nuN N) herror L hL hlevel
  apply hraw.trans
  have hincl := decompJ365_mixed_survivors_le_wCount a b N t t ht le_rfl hthA hthB
  have hincl' : #{i ∈ range N | ∀ p ∈ Nat.primesLE t, ¬ p ∣ i * (N - i)} ≤
      wCount a b N := by simpa using hincl
  exact_mod_cast hincl' 

/-- Second memoir pages 98 and 106 formulas 16.2 and 24.6.
The primes below the final cutoff enter without a further cardinality cap. -/

lemma decomp305_prime_family_complete (x : ℕ → ℝ) (w : ℕ) (c : ℕ → ℕ)
    (hc : Antitone c) (n : ℕ) (hw : c n ≤ w) :
    (∑ S ∈ (Nat.primesLE w).powerset.filter (fun S => ∀ j ∈ range (n + 1),
      (S.filter (fun p => c j < p)).card ≤ 2 * j + 1),
        (-1 : ℝ) ^ S.card * ∏ p ∈ S, x p) =
      (∑ S ∈ decomp305PrimeFamily w c n, (-1 : ℝ) ^ S.card * ∏ p ∈ S, x p) *
        ∏ p ∈ Nat.primesLE (c n), (1 - x p) := by
  let P := (Ioc (c n) w).filter Nat.Prime
  let B := Nat.primesLE (c n)
  have hPB : Disjoint P B := by
    apply disjoint_left.mpr
    intro p hpP hpB
    have hP := mem_Ioc.mp (mem_filter.mp hpP).1
    have hB := (Nat.mem_primesLE.mp hpB).1
    omega
  have hfullP : P ∪ B = Nat.primesLE w := by
    ext p
    simp only [P, B, mem_union, mem_filter, mem_Ioc, Nat.mem_primesLE]
    by_cases hp : p.Prime
    · simp only [hp, and_true]
      omega
    · simp [hp]
  have hmem (V : Finset ℕ) : V ∈ decomp305PrimeFamily w c n ↔ V ⊆ P ∧
      ∀ j ∈ range (n + 1), (V.filter (fun p => c j < p)).card ≤ 2 * j + 1 := by
    simp only [decomp305PrimeFamily, mem_filter, mem_powerset, P]
  have hfilter (S : Finset ℕ) (hS : S ⊆ Nat.primesLE w) (j : ℕ) (hj : j ≤ n) :
      (S ∩ P).filter (fun p => c j < p) = S.filter (fun p => c j < p) := by
    ext p
    simp only [mem_filter, mem_inter]
    constructor
    · tauto
    · rintro ⟨hpS, hpj⟩
      have hpw := Nat.mem_primesLE.mp (hS hpS)
      exact ⟨⟨hpS, mem_filter.mpr ⟨mem_Ioc.mpr ⟨(hc hj).trans_lt hpj, hpw.1⟩,
        hpw.2⟩⟩, hpj⟩
  have hUeq : P.powerset.filter (fun S => S ∈ decomp305PrimeFamily w c n) =
      decomp305PrimeFamily w c n := by
    ext S
    simp only [mem_filter, mem_powerset]
    exact ⟨And.right, fun hS => ⟨((hmem S).mp hS).1, hS⟩⟩
  have hcomplete : (P ∪ B).powerset.filter
      (fun S => S ∩ P ∈ decomp305PrimeFamily w c n) =
      (Nat.primesLE w).powerset.filter (fun S => ∀ j ∈ range (n + 1),
        (S.filter (fun p => c j < p)).card ≤ 2 * j + 1) := by
    rw [hfullP]
    ext S
    simp only [mem_filter, mem_powerset, hmem]
    constructor
    · rintro ⟨hS, _, hcaps⟩
      refine ⟨hS, ?_⟩
      intro j hj
      rw [← hfilter S hS j (by have := mem_range.mp hj; omega)]
      exact hcaps j hj
    · rintro ⟨hS, hcaps⟩
      refine ⟨hS, inter_subset_right, ?_⟩
      intro j hj
      rw [hfilter S hS j (by have := mem_range.mp hj; omega)]
      exact hcaps j hj
  have hh := decomp305_block_extension x P B hPB (fun S => S ∈ decomp305PrimeFamily w c n)
  rw [hcomplete, hUeq] at hh
  exact hh

/-- First memoir pages 75, 88 and 89 and second memoir page 99 formula 18.3.
The normalized actual prime family iteration feeds directly into the actual Z count.
The boundary remains explicit and is not assumed to have a positive balance. -/

private def decomp305HeadMass : ℕ → ℕ
  | 0 => 90
  | 1 => 56
  | 2 => 52
  | _ => 50

/-- Auxiliary scaled factorial convolution for second memoir page 97 formula 15.7.
Only degrees below twice the new block count are retained. -/

private def decomp305HeadStep (t : ℕ) (a : List ℕ) (n : ℕ) : List ℕ :=
  (List.range (2*n)).map fun k => ∑ j ∈ range (k+1), (k.factorial / (j.factorial * (k-j).factorial)) * a[j]?.getD 0 * t^(k-j)

/-- The scaled integer coefficients of the finite factorial lower head.
This is the repeated convolution model for second memoir page 97 formula 15.7. -/

private def decomp305HeadCoeff : ℕ → List ℕ
  | 0 => [1]
  | n+1 => decomp305HeadStep (decomp305HeadMass n) (decomp305HeadCoeff n) (n+1)

/-- The finite signed factorial head, with the integer scaling removed. -/

private def decomp305HeadValue : ℕ → ℚ
  | 0 => 1
  | n + 1 => ∑ k ∈ range (2 * (n + 1)),
      (-1 : ℚ)^k * ((decomp305HeadCoeff (n + 1))[k]?.getD 0 : ℚ) /
        ((100 : ℚ)^k * (k.factorial : ℚ))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- The coefficient model reproduces the printed three block lower head.
First memoir page 81 formula 2.6 and second memoir page 97 formula 15.7. -/

theorem decomp305_head20_positive : (13 / 10000000 : ℚ) < decomp305HeadValue 20 := by
  change (∑ k ∈ range 40, (-1 : ℚ)^k * ((decomp305HeadCoeff 20)[k]?.getD 0 : ℚ) /
    ((100 : ℚ)^k * (k.factorial : ℚ))) > 13/10000000
  have h1 : decomp305HeadCoeff 1 = [1, 90] := by
    decide +kernel
  have h2 : decomp305HeadCoeff 2 = [1, 146, 13216, 1022336] := by
    rw [decomp305HeadCoeff, h1]
    decide +kernel
  have h3 : decomp305HeadCoeff 3 = [1, 198, 31104, 4408992, 516488960, 51944402432] := by
    rw [decomp305HeadCoeff, h2]
    decide +kernel
  have h4 : decomp305HeadCoeff 4 = [1, 248, 53404, 10684592, 1970097360, 336671442432, 49277011729600, 6177744827680000] := by
    rw [decomp305HeadCoeff, h3]
    decide +kernel
  have h5 : decomp305HeadCoeff 5 = [1, 298, 80704, 20680192, 5038325760, 1171128082432, 256355825459200, 52434750110720000, 9351040116668000000, 1431721657242200000000] := by
    rw [decomp305HeadCoeff, h4]
    decide +kernel
  have h6 : decomp305HeadCoeff 6 = [1, 348, 113004, 35145792, 10540174160, 3058219322432, 856472321188800, 230772975549120000, 59071124962624000000, 14200720099494400000000, 3001686005682520000000000, 544780283561168000000000000] := by
    rw [decomp305HeadCoeff, h5]
    decide +kernel
  have h7 : decomp305HeadCoeff 7 = [1, 398, 150304, 54831392, 19444642560, 6724350162432, 2268321378918400, 745676638842880000, 238018943790012000000, 73418051964918600000000, 21612182339001040000000000, 5991303958972278000000000000, 1467011015292012150000000000000, 308264866778414632500000000000000] := by
    rw [decomp305HeadCoeff, h6]
    decide +kernel
  have h8 : decomp305HeadCoeff 8 = [1, 448, 192604, 80486992, 32870730960, 13156925602432, 5166731878648000, 1990712865692000000, 751677412030976000000, 277592242575641600000000, 99859418719345560000000000, 34801498531423620000000000000, 11605036095758616800000000000000, 3649978204519320080000000000000000, 1016740147634251084000000000000000000, 242900617680353793875000000000000000000] := by
    rw [decomp305HeadCoeff, h7]
    decide +kernel
  have h9 : decomp305HeadCoeff 9 = [1, 498, 239904, 112862592, 52087439360, 23641850642432, 10566591700377600, 4652537339796480000, 2017608839497660000000, 861028500188755000000000, 361013135478785680000000000, 148352241986672264000000000000, 59498136379619943750000000000000, 23153336001508718407500000000000000, 8635021521480622078000000000000000000, 3040266057639516635175000000000000000000, 949754944663889455890781250000000000000000, 254294173805276680721539062500000000000000000] := by
    rw [decomp305HeadCoeff, h8]
    decide +kernel
  have h10 : decomp305HeadCoeff 10 = [1, 548, 292204, 152708192, 78513767760, 39801030282432, 19918022724107200, 9846242452856320000, 4808649608582208000000, 2319454008187315200000000, 1104208811767303000000000000, 518220324678411000000000000000, 239316653813165500800000000000000, 108461386130380179840000000000000000, 48033961000901033184000000000000000000, 20661416148180765478275000000000000000000, 8526494157777529669240000000000000000000000, 3323809267809991956438000000000000000000000000, 1151045828033111662247421875000000000000000000000, 341447237960909427682010468750000000000000000000000] := by
    rw [decomp305HeadCoeff, h9]
    decide +kernel
  have h11 : decomp305HeadCoeff 11 = [1, 598, 349504, 200773792, 113718716160, 63629869522432, 35212805829836800, 19285985454571520000, 10457168862456764000000, 5613291024711343400000000, 2982151733713523520000000000, 1567130606795777598000000000000, 813855771530975117750000000000000, 417137498236419838062500000000000000, 210594340752157931533000000000000000000, 104434678773184679183300000000000000000000, 50649258270585402158470781250000000000000000, 23874677961789471852972867187500000000000000000, 10804808388074604196747265625000000000000000000000, 4620860811837047402350698828125000000000000000000000, 1757163139178724887501957730468750000000000000000000000, 572074261088096952902087421289062500000000000000000000000] := by
    rw [decomp305HeadCoeff, h10]
    decide +kernel
  have h12 : decomp305HeadCoeff 12 = [1, 648, 411804, 257809392, 159421284560, 97534773362432, 59102055897566400, 35494834102642080000, 21135290703273472000000, 12479349919228825600000000, 7306138773010950040000000000, 4240171856334529388000000000000, 2438229865700825042400000000000000, 1388203955499603363120000000000000000, 781762893561331259020000000000000000000, 434831980842965740021875000000000000000000, 238400698641023142950000000000000000000000000, 128467790872843349860568000000000000000000000000, 67742909595261862068897421875000000000000000000000, 34736020100938831482838762031250000000000000000000000, 17109540087840069573868826500000000000000000000000000000, 7966012102453531445209591878125000000000000000000000000000, 3300071158363421619966347011464843750000000000000000000000000, 1169927804204789298848272271735351562500000000000000000000000000] := by
    rw [decomp305HeadCoeff, h11]
    decide +kernel
  have h13 : decomp305HeadCoeff 13 = [1, 698, 479104, 324564992, 217490472960, 144370646802432, 95025146807296000, 62057767312768000000, 40227554400364476000000, 25888773425546712600000000, 16541756767399694560000000000, 10492862007341408160000000000000, 6606117108483723380550000000000000, 4126384858336965373117500000000000000, 2555741408681415918789000000000000000000, 1568354041909008580633875000000000000000000, 952529309276266546170050781250000000000000000, 571709441033841661790950195312500000000000000000, 338399611931493742700729121875000000000000000000000, 196961037073546175007633463437500000000000000000000000, 112226994324876639710193769183593750000000000000000000000, 62203497076146823401761029713867187500000000000000000000000, 33131612177137646644996870430781250000000000000000000000000000, 16683937418367294084358552544349609375000000000000000000000000000, 7479364435270197658723881714083172607421875000000000000000000000000, 2868199345330820914624465262861198425292968750000000000000000000000000] := by
    rw [decomp305HeadCoeff, h12]
    decide +kernel
  have h14 : decomp305HeadCoeff 14 = [1, 748, 551404, 401790592, 289945281360, 207478394842432, 147349886439025600, 103921768308649280000, 72814062108441920000000, 50696831290761920000000000, 35079444478013710680000000000, 24123041677097220384000000000000, 16484444345415659072000000000000000, 11191505238452253470720000000000000000, 7546279380604620482848000000000000000000, 5051343060892563076652675000000000000000000, 3354572100336861001592040000000000000000000000, 2208299308212767749180614000000000000000000000000, 1439387612646320606068875421875000000000000000000000, 927545465362092265911810933593750000000000000000000000, 589672890844066225326917824125000000000000000000000000000, 368746946325019867210269485487500000000000000000000000000000, 225813404264542539205668817868027343750000000000000000000000000, 134551012676795191067318489602151367187500000000000000000000000000, 77065974092009181965958161722482812500000000000000000000000000000000, 41737609182868933468892693892618945312500000000000000000000000000000000, 20131966739866575936198926741282628784179687500000000000000000000000000000, 8303633855976014688977448324739619232177734375000000000000000000000000000000] := by
    rw [decomp305HeadCoeff, h13]
    decide +kernel
  have h15 : decomp305HeadCoeff 15 = [1, 798, 628704, 490236192, 378954709760, 290722422482432, 221523941672755200, 167746947771985920000, 126283738595797948000000, 94538641149652328200000000, 70388994319563526000000000000, 52126527896350157750000000000000, 38393791217195138594550000000000000, 28123308490874944315252500000000000000, 20483038849739919142174000000000000000000, 14829453396773552288696400000000000000000000, 10668255702585246269664390781250000000000000000, 7622176003751329715610669523437500000000000000000, 5404952040713476671734173968750000000000000000000000, 3800595731030056475057642696015625000000000000000000000, 2647002223550193634997724512792968750000000000000000000000, 1823166929021837804244094791333007812500000000000000000000000, 1239193713557069497469065446855703125000000000000000000000000000, 828712963294529323449044771583101562500000000000000000000000000000, 542848289351309557829814840201205828857421875000000000000000000000000, 346064883813082631552944773785238075256347656250000000000000000000000000, 212116730647606742377637690605686380004882812500000000000000000000000000000, 122949483115215012851739350502975976974487304687500000000000000000000000000000, 63492357085202893901376027551626458284378051757812500000000000000000000000000000, 28028600133436915191533703194832764982051849365234375000000000000000000000000000000] := by
    rw [decomp305HeadCoeff, h14]
    decide +kernel
  have h16 : decomp305HeadCoeff 16 = [1, 848, 711004, 590651792, 486837758160, 398528134722432, 324237513388484800, 262312634492477920000, 211098902482504704000000, 169034076854007782400000000, 134696374792824474520000000000, 106824300217456883028000000000000, 84319298013801924588000000000000000, 66238421416843912866000000000000000000, 51781618599426440416908000000000000000000, 40276580509719064932822675000000000000000000, 31162963531864182955537120000000000000000000000, 23977089558978338356885344000000000000000000000000, 18337723228058230949588945421875000000000000000000000, 13933248056020356242770635685156250000000000000000000000, 10510322708401441465754642680875000000000000000000000000000, 7864044216449865201330727136990625000000000000000000000000000, 5829468177610147535160478886145214843750000000000000000000000000, 4274478760356324131407938241144848632812500000000000000000000000000, 3093660784420144609976523513031501562500000000000000000000000000000000, 2203437394279316775507214219387227343750000000000000000000000000000000000, 1537519497766415992428942659524206242065429687500000000000000000000000000000, 1044274847429937883482373262862414057769775390625000000000000000000000000000000, 682066511529821320608092079359424235498046875000000000000000000000000000000000000, 421315129400227485407980883728550399386596679687500000000000000000000000000000000000, 231928284248700752056102027699594113241445159912109375000000000000000000000000000000000, 109109371827557864535493865606053702928344001770019531250000000000000000000000000000000000] := by
    rw [decomp305HeadCoeff, h15]
    decide +kernel
  have h17 : decomp305HeadCoeff 17 = [1, 898, 798304, 703787392, 616063426560, 535919436562432, 463597261466214400, 398982371017825280000, 341733923488614332000000, 291375019636401092600000000, 247355329169900429040000000000, 209094244656334906248000000000000, 176010164145445080590150000000000000, 147539860108285788157107500000000000000, 123150753811990442617840000000000000000000, 102348138582506624186384375000000000000000000, 84678827079314966418152050781250000000000000000, 69732307226345453525556490851562500000000000000000, 57140186440746744013192537406250000000000000000000000, 46574508018263326724209614398750000000000000000000000000, 37745342418341074089350570114683593750000000000000000000000, 30397977405790382841122379577072460937500000000000000000000000, 24309886558208935361706827821568203125000000000000000000000000000, 19287692559871151843122824859684435546875000000000000000000000000000, 15164114263953997705598355840789111297607421875000000000000000000000000, 11795193756493896664282149392258206748962402343750000000000000000000000000, 9057392137075357832222077671401900100708007812500000000000000000000000000000, 6845547963462290675748852840876848371154785156250000000000000000000000000000000, 5069566972258535669940376682129283832286453247070312500000000000000000000000000000, 3654796705222841719950081622569750931245975494384765625000000000000000000000000000000, 2534180117630638935861607012102363015934970092773437500000000000000000000000000000000000, 1661904659515242804176863091855288665729247322082519531250000000000000000000000000000000000, 971503927168750457146082898295828670570581730127334594726562500000000000000000000000000000000, 485214438518968135820439635287084344026221919929981231689453125000000000000000000000000000000000] := by
    rw [decomp305HeadCoeff, h16]
    decide +kernel
  have h18 : decomp305HeadCoeff 18 = [1, 948, 890604, 830392992, 769250714960, 708556233002432, 649311479785944000, 592231751803728000000, 537812315192358976000000, 486378710387899033600000000, 438125404866233033560000000000, 393145868186725776200000000000000, 351456177760284966076800000000000000, 313013667807687864689280000000000000000, 277731725744597170181344000000000000000000, 245491567532396557697023875000000000000000000, 216151619147817228254471000000000000000000000000, 189554992069189444296731750000000000000000000000000, 165535425131105241293047666621875000000000000000000000, 143921993268067672219000305776718750000000000000000000000, 124542808196962670254350010924750000000000000000000000000000, 107227909089003623373623544485750000000000000000000000000000000, 91811472010024488933673316312108027343750000000000000000000000000, 78133494366112699904246353927318827148437500000000000000000000000000, 66040988007018484394376969578219831250000000000000000000000000000000000, 55388887890248301890203112814185352539062500000000000000000000000000000000, 46040488997871210122835752089048540206909179687500000000000000000000000000000, 37868008278093670334463664751819953197479248046875000000000000000000000000000000, 30752120470595644987408647760231893683666992187500000000000000000000000000000000000, 24583277122033914679124006261318097361887207031250000000000000000000000000000000000000, 19258180115269878755676645318618631242997048187255859375000000000000000000000000000000000, 14688088591589433893257390546302950951743904685974121093750000000000000000000000000000000000, 10775808151940845005454163049992569454619108642578125000000000000000000000000000000000000000000, 7477368621704160172569189445787764721100314520263671875000000000000000000000000000000000000000000, 4625998448821021285071726996654853793538014264864921569824218750000000000000000000000000000000000000, 2444627697519840756397320185375430632104427761038541793823242187500000000000000000000000000000000000000] := by
    rw [decomp305HeadCoeff, h17]
    decide +kernel
  have h19 : decomp305HeadCoeff 19 = [1, 998, 987904, 971218592, 949168623360, 922771929042432, 892886521227673600, 860243041363886080000, 825468187798350780000000, 789102272979213345000000000, 751612745454326435680000000000, 713404833536914612254000000000000, 674830067310061715997750000000000000, 636193203541201557748282500000000000000, 597757925495970682488243000000000000000000, 559751594278459175786823300000000000000000000, 522369257359415819352214790781250000000000000000, 485777074607126269656991118179687500000000000000000, 450115281869461812970612166234375000000000000000000000, 415500789902595573478203604173828125000000000000000000000, 382029487503541090171492565585355468750000000000000000000000, 349778312210846432033017590611582226562500000000000000000000000, 318807120467917508229595414522645468750000000000000000000000000000, 289160409742415098732101300935734031250000000000000000000000000000000, 260868880950083977039426371186683855828857421875000000000000000000000000, 233950929532022735669740903532949639094543457031250000000000000000000000000, 208413936398528241722120949605244585146484375000000000000000000000000000000000, 184255670571955389043984986504173314150863647460937500000000000000000000000000000, 161465140561125942684379770598856075474702835083007812500000000000000000000000000000, 140024449625734998934576686634024114908469676971435546875000000000000000000000000000000, 119907928197695620977798653746291924329728086853027343750000000000000000000000000000000000, 101087876678816909919888615799596160775226749725341796875000000000000000000000000000000000000, 83522714123157727320084356475382162479349313846826553344726562500000000000000000000000000000000, 67192603057291882470340382169268990800615828662431240081787109375000000000000000000000000000000000, 52001586042483559512744554077103418624141801506676673889160156250000000000000000000000000000000000000, 38066384427159014292583838778558097219997963086097359657287597656250000000000000000000000000000000000000, 24848486197228392846321147241042897551814070228014981746673583984375000000000000000000000000000000000000000, 13852177166574025163211608950655332530106044393691212534904479980468750000000000000000000000000000000000000000] := by
    rw [decomp305HeadCoeff, h18]
    decide +kernel
  have h20 : decomp305HeadCoeff 20 = [1, 1048, 1090204, 1127014192, 1158736151760, 1185610929682432, 1207834472671403200, 1225570509919999520000, 1238959560415781888000000, 1248125498954791731200000000, 1253180487807657519000000000000, 1254228761543497501500000000000000, 1251369566088934479000800000000000000, 1244699449288048608685040000000000000000, 1234314035046330706322764000000000000000000, 1220309376398450276311908275000000000000000000, 1202782957369291588328815440000000000000000000000, 1181834400327337366996946328000000000000000000000000, 1157565923452372688147615169421875000000000000000000000, 1130082589184150321831392820768281250000000000000000000000, 1099492375471916128946470712643750000000000000000000000000000, 1065906104131038443233803968186328125000000000000000000000000000, 1029437247296603965393595243748698964843750000000000000000000000000, 990201647422748959806058473230703711914062500000000000000000000000000, 948317152468925488106947823324607746875000000000000000000000000000000000, 903903224785247625663950966870814921875000000000000000000000000000000000000, 857080461317690210254904439711579279367065429687500000000000000000000000000000, 807970208815825745599392810823684300030548095703125000000000000000000000000000000, 756693911894588107002361505523355772889038085937500000000000000000000000000000000000, 703373072389933513694169129443079818324013061523437500000000000000000000000000000000000, 648127739041144563270369280431798588715324306488037109375000000000000000000000000000000000, 591078764573651401265793699663844678845875191688537597656250000000000000000000000000000000000, 532340259093233864771352590719584893185318642333984375000000000000000000000000000000000000000000, 472038758103797535244940901642796368684307925219726562500000000000000000000000000000000000000000000, 410257502602942685925477129730485743397732568851656913757324218750000000000000000000000000000000000000, 347198020444364054168557098241786205201132634933030366897583007812500000000000000000000000000000000000000, 282691628384004294806178633568078040475546967013246154785156250000000000000000000000000000000000000000000000, 217716189792922609935666503918285744049821222202065224647521972656250000000000000000000000000000000000000000000, 149543403362924358124434504780357400926553298842425744384527206420898437500000000000000000000000000000000000000000, 87704323539661630437993157750912985212893339560154279817640781402587890625000000000000000000000000000000000000000000] := by
    rw [decomp305HeadCoeff, h19]
    decide +kernel
  rw [h20]
  norm_num [sum_range_succ, Nat.factorial]

/-- First memoir page 89, the cumulative printed lower mass from the third block onward. -/

lemma decomp305_head_mass_sum {b : ℕ} (hb : 3 ≤ b) :
    (∑ i ∈ range b, (decomp305HeadMass i : ℝ) / 100) = (b : ℝ) / 2 + 0.48 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hb
  rw [sum_range_add]
  have htail (i : ℕ) : decomp305HeadMass (3 + i) = 50 := by
    rw [show 3 + i = i + 3 by omega]
    rfl
  simp_rw [htail]
  norm_num [sum_range_succ, decomp305HeadMass]
  <;> ring

/-- Auxiliary larger factorial tail for second memoir page 99 formula 18.3.
The shifted mass bounds the printed cumulative masses from the third block onward. -/

private def decomp305CrudeTerm (b : ℕ) : ℝ :=
  exp (((b : ℝ) + 1) / 2) * (((b : ℝ) + 1) / 2) ^ (2 * b) /
    ((2 * b).factorial : ℝ)

/-- Exact consecutive ratio for the auxiliary later tail. -/

lemma decomp305_crude_succ (b : ℕ) :
    decomp305CrudeTerm (b + 1) = decomp305CrudeTerm b * exp (1 / 2 : ℝ) *
      (((b : ℝ) + 2) / ((b : ℝ) + 1)) ^ (2 * b) *
      (((b : ℝ) + 2) ^ 2 / (4 * (2 * b + 2) * (2 * b + 1))) := by
  have hb : (b : ℝ) + 1 ≠ 0 := by positivity
  have hf : ((2 * b).factorial : ℝ) ≠ 0 := by positivity
  have hfac : (2 * (b + 1)).factorial = (2 * b + 2) * (2 * b + 1) * (2 * b).factorial := by
    rw [show 2 * (b + 1) = 2 * b + 1 + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    ring
  have he : (((b + 1 : ℕ) : ℝ) + 1) / 2 = ((b : ℝ) + 1) / 2 + 1 / 2 := by
    push_cast
    ring
  have hp : (((b : ℝ) + 1) / 2) ^ (2 * b) *
      (((b : ℝ) + 2) / ((b : ℝ) + 1)) ^ (2 * b) =
      (((b : ℝ) + 2) / 2) ^ (2 * b) := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hexp : exp ((((b + 1 : ℕ) : ℝ) + 1) / 2) =
      exp (((b : ℝ) + 1) / 2) * exp (1 / 2 : ℝ) := by rw [he, exp_add]
  unfold decomp305CrudeTerm
  rw [hexp, hfac, show 2 * (b + 1) = 2 * b + 2 by omega, pow_add]
  push_cast
  rw [show (((b : ℝ) + 1 + 1) / 2) = ((b : ℝ) + 2) / 2 by ring]
  rw [← hp]
  field_simp
  <;> ring


/-- A geometric ratio valid after the twentieth block.
This is an auxiliary replacement for the late part of the corrected cyclic estimate. -/

lemma decomp305_crude_ratio {b : ℕ} (hb : 20 ≤ b) :
    decomp305CrudeTerm (b + 1) ≤ (0.86 : ℝ) * decomp305CrudeTerm b := by
  have hbR : (20 : ℝ) ≤ b := by exact_mod_cast hb
  have hb1 : (b : ℝ) + 1 ≠ 0 := by positivity
  have hbase : ((b : ℝ) + 2) / ((b : ℝ) + 1) ≤ exp (1 / ((b : ℝ) + 1)) := by
    have hh := add_one_le_exp (1 / ((b : ℝ) + 1))
    convert hh using 1 <;> field_simp <;> ring
  have hpower : (((b : ℝ) + 2) / ((b : ℝ) + 1)) ^ (2 * b) ≤ exp 2 := by
    calc
      _ ≤ exp (1 / ((b : ℝ) + 1)) ^ (2 * b) := pow_le_pow_left₀ (by positivity) hbase _
      _ = exp ((2 * (b : ℝ)) / ((b : ℝ) + 1)) := by
        rw [← exp_nat_mul]
        congr 1
        push_cast
        ring
      _ ≤ exp 2 := exp_le_exp.mpr ((div_le_iff₀ (by positivity)).mpr (by linarith))
  have hfactor : ((b : ℝ) + 2) ^ 2 / (4 * (2 * b + 2) * (2 * b + 1)) ≤ 0.0705 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (show 0 ≤ (b : ℝ) - 20 by linarith) (Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
  have he05 : exp (1 / 2 : ℝ) ≤ 1.649 := ricci_exp_upper_small (by norm_num) (by norm_num)
    (by norm_num [sum_range_succ, Nat.factorial])
  have he2 : exp (2 : ℝ) ≤ 7.39 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, exp_add]
    nlinarith [exp_one_lt_d9, exp_pos (1 : ℝ)]
  have hD : 0 ≤ decomp305CrudeTerm b := by unfold decomp305CrudeTerm; positivity
  rw [decomp305_crude_succ]
  have h1 := mul_le_mul he05 (hpower.trans he2) (by positivity : (0 : ℝ) ≤
    (((b : ℝ) + 2) / ((b : ℝ) + 1)) ^ (2 * b)) (by norm_num : (0 : ℝ) ≤ 1.649)
  have h2 := mul_le_mul h1 hfactor (by positivity : (0 : ℝ) ≤
    ((b : ℝ) + 2) ^ 2 / (4 * (2 * b + 2) * (2 * b + 1)))
    (by norm_num : (0 : ℝ) ≤ 1.649 * 7.39)
  have h3 := mul_le_mul_of_nonneg_left h2 hD
  nlinarith


/-- The auxiliary crude tail from block twenty one onward is below 0.018.
This bounds only the scalar majorant, not the retained sieve main sum. -/

lemma decomp305_crude_tail_lt :
    (∑' k : ℕ, decomp305CrudeTerm (21 + k)) < 0.018 := by
  have he11 : exp (11 : ℝ) ≤ 61000 := by
    calc
      exp (11 : ℝ) = exp (1 : ℝ) ^ (11 : ℕ) := by
        rw [← exp_nat_mul]
        norm_num
      _ ≤ (2.719 : ℝ) ^ (11 : ℕ) :=
        pow_le_pow_left₀ (exp_pos _).le (by linarith [exp_one_lt_d9]) _
      _ ≤ 61000 := by norm_num
  have h21 : decomp305CrudeTerm 21 < 0.0024 := by
    unfold decomp305CrudeTerm
    norm_num only [Nat.cast_ofNat, show ((21 : ℝ) + 1) / 2 = 11 by norm_num]
    have hmul := mul_le_mul_of_nonneg_right he11 (show 0 ≤ (11 : ℝ) ^ (42 : ℕ) by positivity)
    have hdiv := div_le_div_of_nonneg_right hmul
      (show 0 ≤ ((42 : ℕ).factorial : ℝ) by positivity)
    have hnum : (61000 : ℝ) * 11 ^ (42 : ℕ) / ((42 : ℕ).factorial : ℝ) < 0.0024 := by
      norm_num [Nat.factorial]
    convert hdiv.trans_lt hnum using 1 <;> norm_num [Nat.factorial]
  have hshift (k : ℕ) : decomp305CrudeTerm (21 + k) ≤ decomp305CrudeTerm 21 * (0.86 : ℝ) ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        decomp305CrudeTerm (21 + (k + 1)) ≤ 0.86 * decomp305CrudeTerm (21 + k) := by
          simpa only [Nat.add_assoc] using decomp305_crude_ratio (b := 21 + k) (by omega)
        _ ≤ 0.86 * (decomp305CrudeTerm 21 * (0.86 : ℝ) ^ k) := by gcongr
        _ = decomp305CrudeTerm 21 * (0.86 : ℝ) ^ (k + 1) := by ring
  have hdom : Summable (fun k : ℕ => decomp305CrudeTerm 21 * (0.86 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(0.86 : ℝ)‖ < 1)).mul_left _
  have hsum : Summable (fun k : ℕ => decomp305CrudeTerm (21 + k)) :=
    hdom.of_nonneg_of_le (fun k => by unfold decomp305CrudeTerm; positivity) hshift
  have hle := hsum.tsum_le_tsum hshift hdom
  rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (by norm_num : |(0.86 : ℝ)| < 1)] at hle
  have hupper : decomp305CrudeTerm 21 * (1 - (0.86 : ℝ))⁻¹ < 0.018 := by
    norm_num
    linarith
  exact hle.trans_lt hupper

/-- Auxiliary longer head certificate for second memoir page 99 formula 18.3.
The exact factorial head minus the full later scalar majorant is positive.
No comparison with the actual sieve boundary is assumed or asserted here. -/

lemma decomp305_pair_product_lower (h y w : ℕ) (hy : 4 ≤ y) :
    exp (-(∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p) - 8 / (y : ℝ)) ≤
      ∏ p ∈ (Ioc y w).filter Nat.Prime, (1 - nuN h p) := by
  let P := (Ioc y w).filter Nat.Prime
  have hy0 : y ≠ 0 := by omega
  have hlocal (p : ℕ) (hp : p ∈ P) :
      0 ≤ nuN h p ∧ nuN h p ≤ 2 / (p : ℝ) ∧ nuN h p ≤ 1 / 2 := by
    have hprime := (mem_filter.mp hp).2
    have hpy := (mem_Ioc.mp (mem_filter.mp hp).1).1
    have hpR : (4 : ℝ) ≤ p := by exact_mod_cast (by omega : 4 ≤ p)
    have hp0 : (0 : ℝ) < p := by positivity
    have hu : nuN h p ≤ 2 / (p : ℝ) := by
      rw [nuN_prime hprime]
      exact div_le_div_of_nonneg_right (wt_le_two h p) (Nat.cast_nonneg p)
    refine ⟨nuN_nonneg h p, hu, hu.trans ?_⟩
    rw [div_le_iff₀ hp0]
    linarith
  have hsq : (∑ p ∈ P, (nuN h p) ^ 2) ≤ 4 / (y : ℝ) := by
    by_cases hyw : y ≤ w
    · have htail := sum_Ioc_inv_sq_le_sub (α := ℝ) hy0 hyw
      have htail' : (∑ p ∈ Ioc y w, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1 / (y : ℝ) := by
        simp only [one_div] at htail ⊢
        have hw0 : (0 : ℝ) ≤ (w : ℝ)⁻¹ := by positivity
        linarith
      have hterm : ∀ p ∈ P, (nuN h p) ^ 2 ≤ 4 * (1 / (p : ℝ) ^ 2) := by
        intro p hp
        have hh := pow_le_pow_left₀ (hlocal p hp).1 (hlocal p hp).2.1 2
        simpa only [div_pow, show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num, mul_one_div] using hh
      have hsub : (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) ≤
          ∑ p ∈ Ioc y w, (1 : ℝ) / (p : ℝ) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => by positivity)
      calc
        _ ≤ ∑ p ∈ P, 4 * (1 / (p : ℝ) ^ 2) := sum_le_sum hterm
        _ = 4 * ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2 := by rw [mul_sum]
        _ ≤ 4 * (1 / (y : ℝ)) := mul_le_mul_of_nonneg_left (hsub.trans htail') (by norm_num)
        _ = 4 / (y : ℝ) := by ring
    · have hP : P = ∅ := by simp [P, Ioc_eq_empty (by omega : ¬ y < w)]
      simp only [hP, sum_empty]
      positivity
  have hp := LeanLab.PNTSieve.Mertens.prod_one_sub_ge_exp P (nuN h)
    (fun p hp => (hlocal p hp).1) (fun p hp => (hlocal p hp).2.2)
  apply le_trans (exp_le_exp.mpr ?_) hp
  change -(∑ p ∈ P, nuN h p) - 8 / (y : ℝ) ≤
    -(∑ p ∈ P, nuN h p + 2 * ∑ p ∈ P, (nuN h p) ^ 2)
  have hh : 2 * (∑ p ∈ P, (nuN h p) ^ 2) ≤ 8 / (y : ℝ) := by
    calc
      _ ≤ 2 * (4 / (y : ℝ)) := mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = 8 / (y : ℝ) := by ring
  linarith only [hh]

/-- Second memoir pages 95 and 97 formula 15.6, unsigned block coefficient expansion. -/

lemma decomp305_esymm_block_convolution (x : ℕ → ℝ) (P B : Finset ℕ)
    (hPB : Disjoint P B) (r : ℕ) :
    LeanLab.PNTSieve.Bonferroni.esymm x (P ∪ B) r =
      ∑ S ∈ P.powerset.filter (fun S => S.card ≤ r), (∏ p ∈ S, x p) *
        LeanLab.PNTSieve.Bonferroni.esymm x B (r - S.card) := by
  change (∑ V ∈ (P ∪ B).powersetCard r, ∏ p ∈ V, x p) = _
  rw [powersetCard_eq_filter, sum_filter, decomp305_disjoint_powerset_sum P B hPB, sum_filter]
  apply sum_congr rfl
  intro S hS
  have hSP : S ⊆ P := mem_powerset.mp hS
  by_cases hSr : S.card ≤ r
  · rw [if_pos hSr]
    unfold LeanLab.PNTSieve.Bonferroni.esymm
    rw [powersetCard_eq_filter, sum_filter, mul_sum]
    apply sum_congr rfl
    intro T hT
    have hTB : T ⊆ B := mem_powerset.mp hT
    have hST : Disjoint S T := hPB.mono hSP hTB
    have heq : S.card + T.card = r ↔ T.card = r - S.card := by omega
    simp only [card_union_of_disjoint hST, prod_union hST, heq, mul_ite, mul_zero]
  · rw [if_neg hSr]
    apply sum_eq_zero
    intro T hT
    have hTB : T ⊆ B := mem_powerset.mp hT
    have hST : Disjoint S T := hPB.mono hSP hTB
    have hne : S.card + T.card ≠ r := by omega
    simp only [card_union_of_disjoint hST, hne, ite_false]


/-- Second memoir pages 95 and 99, a crude unsigned boundary bound.
Discarding the old prefix restrictions bounds the coefficient by the full factorial monomial. -/

lemma decomp305_pair_coefficient_normalized (h y w b : ℕ) (hy : 4 ≤ y)
    (hmass : (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p) ≤ ((b : ℝ) + 1) / 2) :
    LeanLab.PNTSieve.Bonferroni.esymm (nuN h) ((Ioc y w).filter Nat.Prime) (2 * b) /
        (∏ p ∈ (Ioc y w).filter Nat.Prime, (1 - nuN h p)) ≤
      exp (8 / (y : ℝ)) * decomp305CrudeTerm b := by
  let P := (Ioc y w).filter Nat.Prime
  let M := ∑ p ∈ P, nuN h p
  have hM : 0 ≤ M := sum_nonneg (fun p _ => nuN_nonneg h p)
  have hprod := decomp305_pair_product_lower h y w hy
  have hprod0 : 0 < ∏ p ∈ P, (1 - nuN h p) :=
    (exp_pos _).trans_le hprod
  have he : LeanLab.PNTSieve.Bonferroni.esymm (nuN h) P (2 * b) ≤
      M ^ (2 * b) / ((2 * b).factorial : ℝ) := by
    rw [le_div_iff₀ (by positivity)]
    have hh := LeanLab.PNTSieve.Bonferroni.factorial_mul_esymm_le
      (nuN h) (nuN_nonneg h) P (2 * b)
    nlinarith
  have hbound : exp M * (M ^ (2 * b) / ((2 * b).factorial : ℝ)) ≤ decomp305CrudeTerm b := by
    have hh := mul_le_mul (exp_le_exp.mpr hmass) (pow_le_pow_left₀ hM hmass (2 * b))
      (pow_nonneg hM _) (exp_pos (((b : ℝ) + 1) / 2)).le
    have hd := div_le_div_of_nonneg_right hh
      (show 0 ≤ ((2 * b).factorial : ℝ) by positivity)
    simpa only [decomp305CrudeTerm, mul_div_assoc] using hd
  change LeanLab.PNTSieve.Bonferroni.esymm (nuN h) P (2 * b) /
    (∏ p ∈ P, (1 - nuN h p)) ≤ exp (8 / (y : ℝ)) * decomp305CrudeTerm b
  calc
    _ ≤ (M ^ (2 * b) / ((2 * b).factorial : ℝ)) /
        (∏ p ∈ P, (1 - nuN h p)) := div_le_div_of_nonneg_right he hprod0.le
    _ ≤ (M ^ (2 * b) / ((2 * b).factorial : ℝ)) / exp (-M - 8 / (y : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) (exp_pos _) hprod
    _ = exp (8 / (y : ℝ)) * (exp M * (M ^ (2 * b) / ((2 * b).factorial : ℝ))) := by
      rw [div_eq_mul_inv, ← exp_neg, show -(-M - 8 / (y : ℝ)) = M + 8 / (y : ℝ) by ring, exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (exp_pos _).le

/-- Second memoir page 99 formula 18.3, exact identification of successive density products. -/

lemma decomp305_prime_product_iteration (x : ℕ → ℝ) (w : ℕ) (c : ℕ → ℕ)
    (hc : Antitone c) (hw : c 0 ≤ w) (s n : ℕ) :
    (∏ p ∈ (Ioc (c (s + n)) w).filter Nat.Prime, (1 - x p)) =
      (∏ p ∈ (Ioc (c s) w).filter Nat.Prime, (1 - x p)) *
        ∏ j ∈ range n, ∏ p ∈ (Ioc (c (s + j + 1)) (c (s + j))).filter Nat.Prime,
          (1 - x p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcur : c (s + n) ≤ w := (hc (Nat.zero_le _)).trans hw
    have hnext : c (s + n + 1) ≤ c (s + n) := hc (by omega)
    have hsets : (Ioc (c (s + n + 1)) w).filter Nat.Prime =
        ((Ioc (c (s + n)) w).filter Nat.Prime) ∪
          ((Ioc (c (s + n + 1)) (c (s + n))).filter Nat.Prime) := by
      ext p
      simp only [mem_filter, mem_Ioc, mem_union]
      by_cases hp : p.Prime
      · simp only [hp, and_true]
        omega
      · simp [hp]
    have hdisj : Disjoint ((Ioc (c (s + n)) w).filter Nat.Prime)
        ((Ioc (c (s + n + 1)) (c (s + n))).filter Nat.Prime) := by
      apply disjoint_left.mpr
      intro p hp hq
      have hp' := mem_Ioc.mp (mem_filter.mp hp).1
      have hq' := mem_Ioc.mp (mem_filter.mp hq).1
      omega
    rw [show s + (n + 1) = s + n + 1 by omega, hsets, prod_union hdisj, ih, prod_range_succ]
    ring

/-- Second memoir pages 95, 99 and 109, the actual first omitted boundary.
The full cumulative mass budget gives the shifted factorial scalar majorant. -/

lemma decomp305_pair_boundary_normalized (h w : ℕ) (c : ℕ → ℕ) (hc : Antitone c)
    (i : ℕ) (hw : c i ≤ w) (hy : 4 ≤ c (i + 1))
    (hmass : (∑ p ∈ (Ioc (c (i + 1)) w).filter Nat.Prime, nuN h p) ≤
      (((i + 2 : ℕ) : ℝ) + 1) / 2) :
    (∑ S ∈ decomp305PrimeFamily w c i, (∏ p ∈ S, nuN h p) *
      LeanLab.PNTSieve.Bonferroni.esymm (nuN h)
        ((Ioc (c (i + 1)) (c i)).filter Nat.Prime)
        (2 * (i + 1) + 1 - S.card + 1)) /
      (∏ p ∈ (Ioc (c (i + 1)) w).filter Nat.Prime, (1 - nuN h p)) ≤
      exp (8 / (c (i + 1) : ℝ)) * decomp305CrudeTerm (i + 2) := by
  let P := (Ioc (c i) w).filter Nat.Prime
  let B := (Ioc (c (i + 1)) (c i)).filter Nat.Prime
  let Q := (Ioc (c (i + 1)) w).filter Nat.Prime
  let U := decomp305PrimeFamily w c i
  have hnext : c (i + 1) ≤ c i := hc (by omega)
  have hsets : P ∪ B = Q := by
    dsimp [P, B, Q]
    rw [← filter_union, union_comm, Ioc_union_Ioc_eq_Ioc hnext hw]
  have hPB : Disjoint P B := by
    apply disjoint_left.mpr
    intro p hp hq
    have hp' := mem_Ioc.mp (mem_filter.mp hp).1
    have hq' := mem_Ioc.mp (mem_filter.mp hq).1
    omega
  have hsub : U ⊆ P.powerset.filter (fun S => S.card ≤ 2 * (i + 2)) := by
    intro S hS
    have hcard := decomp305_prime_family_card w c i S hS
    have hSP : S ⊆ P := by
      have hs : S ∈ decomp305PrimeFamily w c i := hS
      simp only [decomp305PrimeFamily, mem_filter, mem_powerset] at hs
      exact hs.1
    exact mem_filter.mpr ⟨mem_powerset.mpr hSP, by omega⟩
  have hPhi : (∑ S ∈ U, (∏ p ∈ S, nuN h p) *
      LeanLab.PNTSieve.Bonferroni.esymm (nuN h) B
        (2 * (i + 1) + 1 - S.card + 1)) ≤
      LeanLab.PNTSieve.Bonferroni.esymm (nuN h) Q (2 * (i + 2)) := by
    calc
      _ = ∑ S ∈ U, (∏ p ∈ S, nuN h p) *
          LeanLab.PNTSieve.Bonferroni.esymm (nuN h) B (2 * (i + 2) - S.card) := by
        apply sum_congr rfl
        intro S hS
        have hcard := decomp305_prime_family_card w c i S hS
        rw [show 2 * (i + 1) + 1 - S.card + 1 = 2 * (i + 2) - S.card by omega]
      _ ≤ ∑ S ∈ P.powerset.filter (fun S => S.card ≤ 2 * (i + 2)), (∏ p ∈ S, nuN h p) *
          LeanLab.PNTSieve.Bonferroni.esymm (nuN h) B (2 * (i + 2) - S.card) := by
        apply sum_le_sum_of_subset_of_nonneg hsub
        intro S _ _
        exact mul_nonneg (prod_nonneg (fun p _ => nuN_nonneg h p))
          (LeanLab.PNTSieve.Bonferroni.esymm_nonneg (nuN h) (nuN_nonneg h) B _)
      _ = LeanLab.PNTSieve.Bonferroni.esymm (nuN h) (P ∪ B) (2 * (i + 2)) :=
        (decomp305_esymm_block_convolution (nuN h) P B hPB _).symm
      _ = _ := by rw [hsets]
  have hprod0 : 0 < ∏ p ∈ Q, (1 - nuN h p) :=
    (exp_pos _).trans_le (decomp305_pair_product_lower h (c (i + 1)) w hy)
  change (∑ S ∈ U, (∏ p ∈ S, nuN h p) *
    LeanLab.PNTSieve.Bonferroni.esymm (nuN h) B (2 * (i + 1) + 1 - S.card + 1)) /
      (∏ p ∈ Q, (1 - nuN h p)) ≤ _
  exact (div_le_div_of_nonneg_right hPhi hprod0.le).trans
    (decomp305_pair_coefficient_normalized h (c (i + 1)) w (i + 2) hy hmass)

lemma decomp338_retained_degree_convolution (x : ℕ → ℝ) (P B : Finset ℕ)
    (hPB : Disjoint P B) (A : Finset ℕ → Prop) [DecidablePred A] (k : ℕ) :
    (∑ V ∈ (P ∪ B).powerset.filter (fun V => A (V ∩ P) ∧ V.card = k),
      ∏ p ∈ V, x p) =
      ∑ j ∈ range (k + 1),
        (∑ S ∈ P.powerset.filter (fun S => A S ∧ S.card = j), ∏ p ∈ S, x p) *
          esymm x B (k - j) := by
  rw [sum_filter, decomp305_disjoint_powerset_sum P B hPB]
  have hleft : (∑ S ∈ P.powerset, ∑ T ∈ B.powerset,
      if A ((S ∪ T) ∩ P) ∧ (S ∪ T).card = k then ∏ p ∈ S ∪ T, x p else 0) =
      ∑ S ∈ P.powerset.filter (fun S => A S ∧ S.card ≤ k),
        (∏ p ∈ S, x p) * esymm x B (k - S.card) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro S hS
    have hSP := mem_powerset.mp hS
    have hint (T : Finset ℕ) (hT : T ∈ B.powerset) : (S ∪ T) ∩ P = S := by
      have hTP := (hPB.mono_right (mem_powerset.mp hT)).symm
      rw [union_inter_distrib_right, inter_eq_left.mpr hSP,
        disjoint_iff_inter_eq_empty.mp hTP, union_empty]
    by_cases hAS : A S ∧ S.card ≤ k
    · rw [if_pos hAS]
      unfold esymm
      rw [powersetCard_eq_filter, sum_filter, mul_sum]
      apply sum_congr rfl
      intro T hT
      have hST := hPB.mono hSP (mem_powerset.mp hT)
      have hcard : S.card + T.card = k ↔ T.card = k - S.card := by omega
      rw [hint T hT, card_union_of_disjoint hST, prod_union hST]
      simp only [hAS.1, true_and, hcard, mul_ite, mul_zero]
    · rw [if_neg hAS]
      apply sum_eq_zero
      intro T hT
      have hST := hPB.mono hSP (mem_powerset.mp hT)
      rw [hint T hT, card_union_of_disjoint hST]
      apply if_neg
      intro h
      exact hAS ⟨h.1, by omega⟩
  rw [hleft]
  symm
  calc
    _ = ∑ j ∈ range (k + 1),
        ∑ S ∈ (P.powerset.filter (fun S => A S ∧ S.card ≤ k)).filter
            (fun S => S.card = j), (∏ p ∈ S, x p) * esymm x B (k - S.card) := by
      apply sum_congr rfl
      intro j hj
      rw [sum_mul]
      apply sum_congr
      · ext S
        simp only [mem_filter]
        have hjk : j ≤ k := by have := mem_range.mp hj; omega
        aesop
      · intro S hS
        have hSj := (mem_filter.mp hS).2
        simp only [hSj]
    _ = _ := sum_fiberwise_of_maps_to
      (fun S hS => mem_range.mpr (by have := (mem_filter.mp hS).2.2; omega)) _


/-- Auxiliary block limit for second memoir pages 97 and 111 formula 28.11.
Convergence of every old degree coefficient and of the new block moments gives
convergence of the next retained degree coefficient. -/

private def decomp338PrimeCoeff (x : ℕ → ℝ) (w : ℕ) (c : ℕ → ℕ) (n k : ℕ) : ℝ :=
  ∑ S ∈ (decomp305PrimeFamily w c n).filter (fun S => S.card = k), ∏ p ∈ S, x p

/-- Second memoir page 97 formula 15.7 for the actual decreasing prime family. -/

lemma decomp338_prime_coeff_step (x : ℕ → ℝ) (w : ℕ) (c : ℕ → ℕ)
    (hc : Antitone c) (n k : ℕ) (hw : c n ≤ w) (hk : k ≤ 2 * (n + 1) + 1) :
    decomp338PrimeCoeff x w c (n + 1) k =
      ∑ j ∈ range (k + 1), decomp338PrimeCoeff x w c n j *
        esymm x ((Ioc (c (n + 1)) (c n)).filter Nat.Prime) (k - j) := by
  let P := (Ioc (c n) w).filter Nat.Prime
  let B := (Ioc (c (n + 1)) (c n)).filter Nat.Prime
  have hPB : Disjoint P B := by
    apply disjoint_left.mpr
    intro p hp hq
    have hpI := mem_Ioc.mp (mem_filter.mp hp).1
    have hqI := mem_Ioc.mp (mem_filter.mp hq).1
    omega
  have hfilter : (decomp305PrimeFamily w c (n + 1)).filter (fun S => S.card = k) =
      (P ∪ B).powerset.filter (fun V => V ∩ P ∈ decomp305PrimeFamily w c n ∧ V.card = k) := by
    rw [decomp305_prime_family_step w c hc n hw]
    ext V
    simp only [mem_filter, P, B]
    constructor
    · rintro ⟨⟨hV, hA, hcap⟩, hVk⟩
      exact ⟨hV, hA, hVk⟩
    · rintro ⟨hV, hA, hVk⟩
      exact ⟨⟨hV, hA, by omega⟩, hVk⟩
  unfold decomp338PrimeCoeff
  rw [hfilter, decomp338_retained_degree_convolution x P B hPB]
  apply sum_congr rfl
  intro j hj
  congr 1
  congr 1
  ext S
  simp only [mem_filter, mem_powerset]
  constructor
  · rintro ⟨hSP, hS, hj⟩
    exact ⟨hS, hj⟩
  · rintro ⟨hS, hj⟩
    have hSP : S ⊆ P := by
      have hs := hS
      simp only [decomp305PrimeFamily, mem_filter, mem_powerset] at hs
      exact hs.1
    exact ⟨hSP, hS, hj⟩

/-- Second memoir page 97 formula 15.5 for the actual retained prime family.
Grouping by degree keeps the signed head exact. -/

lemma decomp338_prime_head_by_degree (x : ℕ → ℝ) (w : ℕ) (c : ℕ → ℕ) (n : ℕ) :
    (∑ S ∈ decomp305PrimeFamily w c n, (-1 : ℝ) ^ S.card * ∏ p ∈ S, x p) =
      ∑ k ∈ range (2 * (n + 1)), (-1 : ℝ) ^ k * decomp338PrimeCoeff x w c n k := by
  symm
  calc
    _ = ∑ k ∈ range (2 * (n + 1)),
        ∑ S ∈ (decomp305PrimeFamily w c n).filter (fun S => S.card = k),
          (-1 : ℝ) ^ S.card * ∏ p ∈ S, x p := by
      apply sum_congr rfl
      intro k hk
      rw [decomp338PrimeCoeff, mul_sum]
      apply sum_congr rfl
      intro S hS
      rw [(mem_filter.mp hS).2]
    _ = _ := sum_fiberwise_of_maps_to (fun S hS => mem_range.mpr
      (by have := decomp305_prime_family_card w c n S hS; omega)) _


/-- Auxiliary scaling identity for second memoir page 97 formula 15.7.
The integer convolution becomes the factorial convolution after removing its scale. -/

lemma decomp338_scaled_convolution (a : ℕ → ℕ) (t k : ℕ) :
    ((∑ j ∈ range (k + 1),
      (k.factorial / (j.factorial * (k - j).factorial)) * a j * t ^ (k - j) : ℕ) : ℝ) /
      ((100 : ℝ) ^ k * (k.factorial : ℝ)) =
      ∑ j ∈ range (k + 1),
        ((a j : ℝ) / ((100 : ℝ) ^ j * (j.factorial : ℝ))) *
          (((t : ℝ) / 100) ^ (k - j) / ((k - j).factorial : ℝ)) := by
  push_cast
  rw [sum_div]
  apply sum_congr rfl
  intro j hj
  have hjk : j ≤ k := by have := mem_range.mp hj; omega
  rw [Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial hjk) (by positivity)]
  push_cast
  have hp : (100 : ℝ) ^ k = 100 ^ j * 100 ^ (k - j) := by
    rw [← pow_add, Nat.add_sub_of_le hjk]
  rw [hp, div_pow]
  field_simp <;> ring

/-- Auxiliary coefficient recurrence for second memoir page 97 formula 15.7.
The existing integer list has the exact factorial convolution at every retained degree. -/

lemma decomp338_head_coeff_step (n k : ℕ) (hk : k < 2 * (n + 1)) :
    (((decomp305HeadCoeff (n + 1))[k]?.getD 0 : ℕ) : ℝ) /
      ((100 : ℝ) ^ k * (k.factorial : ℝ)) =
      ∑ j ∈ range (k + 1),
        ((((decomp305HeadCoeff n)[j]?.getD 0 : ℕ) : ℝ) /
          ((100 : ℝ) ^ j * (j.factorial : ℝ))) *
        (((decomp305HeadMass n : ℝ) / 100) ^ (k - j) / ((k - j).factorial : ℝ)) := by
  rw [decomp305HeadCoeff, decomp305HeadStep, List.getElem?_map, List.getElem?_range hk]
  simp only [Option.map_some, Option.getD_some]
  exact decomp338_scaled_convolution _ _ _

/-- Auxiliary support of the integer coefficient list for second memoir page 97 formula 15.7. -/

lemma decomp338_head_coeff_length (n : ℕ) :
    (decomp305HeadCoeff (n + 1)).length = 2 * (n + 1) := by
  simp [decomp305HeadCoeff, decomp305HeadStep]


/-- Second memoir page 97 formula 14.8, the last odd cap removes every higher degree. -/

lemma decomp338_prime_coeff_eq_zero (x : ℕ → ℝ) (w : ℕ) (c : ℕ → ℕ)
    (n k : ℕ) (hk : 2 * n + 1 < k) : decomp338PrimeCoeff x w c n k = 0 := by
  unfold decomp338PrimeCoeff
  apply sum_eq_zero
  intro S hS
  obtain ⟨hS, hSk⟩ := mem_filter.mp hS
  have := decomp305_prime_family_card w c n S hS
  omega

/-- Second memoir page 97 formula 15.7 at the first odd cap.
The initial retained coefficient is the unrestricted symmetric coefficient through degree one. -/

lemma decomp338_prime_coeff_initial (x : ℕ → ℝ) (w : ℕ) (c : ℕ → ℕ)
    (k : ℕ) (hk : k ≤ 1) :
    decomp338PrimeCoeff x w c 0 k = esymm x ((Ioc (c 0) w).filter Nat.Prime) k := by
  unfold decomp338PrimeCoeff esymm
  congr 1
  ext S
  constructor
  · intro h
    obtain ⟨hS, hSk⟩ := mem_filter.mp h
    have hs := hS
    simp only [decomp305PrimeFamily, mem_filter, mem_powerset] at hs
    exact mem_powersetCard.mpr ⟨hs.1, hSk⟩
  · intro h
    obtain ⟨hSP, hSk⟩ := mem_powersetCard.mp h
    apply mem_filter.mpr
    refine ⟨?_, hSk⟩
    simp only [decomp305PrimeFamily, mem_filter, mem_powerset]
    refine ⟨hSP, ?_⟩
    intro j hj
    have hj0 : j = 0 := by simpa using mem_range.mp hj
    subst j
    exact (card_filter_le _ _).trans (by omega)


/-- Prime blocks in the lower decreasing sieve of second memoir pages 92 and 97.
Block zero is above the first cutoff. Each later block lies between consecutive cutoffs. -/

private def decomp338PrimeBlock (w : ℕ) (c : ℕ → ℕ) : ℕ → Finset ℕ
  | 0 => (Ioc (c 0) w).filter Nat.Prime
  | i + 1 => (Ioc (c (i + 1)) (c i)).filter Nat.Prime

/-- Auxiliary finite head limit in second memoir page 111 formula 28.11.
Every actual retained degree coefficient tends to its scaled integer factorial model. -/

lemma decomp338_prime_coeff_tendsto (x : ℕ → ℕ → ℝ)
    (w : ℕ → ℕ) (c : ℕ → ℕ → ℕ)
    (hc : ∀ q, Antitone (c q)) (hw : ∀ q, c q 0 ≤ w q)
    (hx : ∀ q p, 0 ≤ x q p)
    (ht : ∀ i, Tendsto (fun q => ∑ p ∈ decomp338PrimeBlock (w q) (c q) i, x q p)
      atTop (nhds ((decomp305HeadMass i : ℝ) / 100)))
    (hq : ∀ i, Tendsto (fun q => ∑ p ∈ decomp338PrimeBlock (w q) (c q) i, (x q p) ^ 2)
      atTop (nhds 0)) (n k : ℕ) :
    Tendsto (fun q => decomp338PrimeCoeff (x q) (w q) (c q) n k) atTop
      (nhds ((((decomp305HeadCoeff (n + 1))[k]?.getD 0 : ℕ) : ℝ) /
        ((100 : ℝ) ^ k * (k.factorial : ℝ)))) := by
  induction n generalizing k with
  | zero =>
    by_cases hk : k ≤ 1
    · have heq : (fun q => decomp338PrimeCoeff (x q) (w q) (c q) 0 k) =
          (fun q => esymm (x q) (decomp338PrimeBlock (w q) (c q) 0) k) := by
        funext q
        exact decomp338_prime_coeff_initial (x q) (w q) (c q) k hk
      rw [heq]
      have hl := decompJ365_esymm_tendsto x
        (fun q => decomp338PrimeBlock (w q) (c q) 0) hx
        ((decomp305HeadMass 0 : ℝ) / 100) (ht 0) (hq 0) k
      convert hl using 1
      interval_cases k <;> norm_num [decomp305HeadCoeff, decomp305HeadStep,
        decomp305HeadMass, sum_range_succ]
    · have hk' : 1 < k := by omega
      have heq : (fun q => decomp338PrimeCoeff (x q) (w q) (c q) 0 k) =
          (fun _ : ℕ => (0 : ℝ)) := by
        funext q
        exact decomp338_prime_coeff_eq_zero (x q) (w q) (c q) 0 k (by omega)
      rw [heq, List.getElem?_eq_none (by rw [decomp338_head_coeff_length]; omega)]
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  | succ n ih =>
    by_cases hk : k < 2 * (n + 1 + 1)
    · have heq : (fun q => decomp338PrimeCoeff (x q) (w q) (c q) (n + 1) k) =
          (fun q => ∑ j ∈ range (k + 1),
            decomp338PrimeCoeff (x q) (w q) (c q) n j *
              esymm (x q) (decomp338PrimeBlock (w q) (c q) (n + 1)) (k - j)) := by
        funext q
        exact decomp338_prime_coeff_step (x q) (w q) (c q) (hc q) n k
          ((hc q (Nat.zero_le n)).trans (hw q)) (by omega)
      rw [heq, decomp338_head_coeff_step (n + 1) k hk]
      apply tendsto_finsetSum
      intro j hj
      exact (ih j).mul (decompJ365_esymm_tendsto x
        (fun q => decomp338PrimeBlock (w q) (c q) (n + 1)) hx
        ((decomp305HeadMass (n + 1) : ℝ) / 100) (ht (n + 1)) (hq (n + 1)) (k - j))
    · have heq : (fun q => decomp338PrimeCoeff (x q) (w q) (c q) (n + 1) k) =
          (fun _ : ℕ => (0 : ℝ)) := by
        funext q
        exact decomp338_prime_coeff_eq_zero (x q) (w q) (c q) (n + 1) k (by omega)
      rw [heq, List.getElem?_eq_none (by rw [decomp338_head_coeff_length]; omega)]
      simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))


/-- Auxiliary finite head limit in second memoir page 111 formula 28.11.
At every fixed block count the actual signed retained head tends to its exact factorial model. -/

lemma decomp338_prime_head_tendsto (x : ℕ → ℕ → ℝ)
    (w : ℕ → ℕ) (c : ℕ → ℕ → ℕ)
    (hc : ∀ q, Antitone (c q)) (hw : ∀ q, c q 0 ≤ w q)
    (hx : ∀ q p, 0 ≤ x q p)
    (ht : ∀ i, Tendsto (fun q => ∑ p ∈ decomp338PrimeBlock (w q) (c q) i, x q p)
      atTop (nhds ((decomp305HeadMass i : ℝ) / 100)))
    (hq : ∀ i, Tendsto (fun q => ∑ p ∈ decomp338PrimeBlock (w q) (c q) i, (x q p) ^ 2)
      atTop (nhds 0)) (n : ℕ) :
    Tendsto (fun q => ∑ S ∈ decomp305PrimeFamily (w q) (c q) n,
      (-1 : ℝ) ^ S.card * ∏ p ∈ S, x q p) atTop (nhds (decomp305HeadValue (n + 1) : ℝ)) := by
  have heq : (fun q => ∑ S ∈ decomp305PrimeFamily (w q) (c q) n,
      (-1 : ℝ) ^ S.card * ∏ p ∈ S, x q p) =
      (fun q => ∑ k ∈ range (2 * (n + 1)),
        (-1 : ℝ) ^ k * decomp338PrimeCoeff (x q) (w q) (c q) n k) := by
    funext q
    exact decomp338_prime_head_by_degree (x q) (w q) (c q) n
  have hv : (decomp305HeadValue (n + 1) : ℝ) =
      ∑ k ∈ range (2 * (n + 1)), (-1 : ℝ) ^ k *
        ((((decomp305HeadCoeff (n + 1))[k]?.getD 0 : ℕ) : ℝ) /
          ((100 : ℝ) ^ k * (k.factorial : ℝ))) := by
    rw [decomp305HeadValue]
    push_cast
    apply sum_congr rfl
    intro k hk
    ring
  rw [heq, hv]
  apply tendsto_finsetSum
  intro k hk
  exact tendsto_const_nhds.mul
    (decomp338_prime_coeff_tendsto x w c hc hw hx ht hq n k)

lemma decomp338_head_mass_pos (i : ℕ) : 0 < (decomp305HeadMass i : ℝ) / 100 := by
  rcases i with _ | i
  · norm_num [decomp305HeadMass]
  rcases i with _ | i
  · norm_num [decomp305HeadMass]
  rcases i with _ | i
  · norm_num [decomp305HeadMass]
  · norm_num [decomp305HeadMass]

/-- Auxiliary actual block moment construction for second memoir pages 109 to 111.
The printed masses and vanishing square masses are realized by decreasing prime cutoffs. -/

lemma decomp338_prime_mass_telescopes (x : ℕ → ℝ) (e : ℕ → ℕ)
    (he : Antitone e) (n : ℕ) :
    (∑ i ∈ range n, ∑ p ∈ (Ioc (e (i + 1)) (e i)).filter Nat.Prime, x p) =
      ∑ p ∈ (Ioc (e n) (e 0)).filter Nat.Prime, x p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    have hsets : (Ioc (e (n + 1)) (e 0)).filter Nat.Prime =
        (Ioc (e n) (e 0)).filter Nat.Prime ∪
          (Ioc (e (n + 1)) (e n)).filter Nat.Prime := by
      rw [← filter_union, union_comm, Ioc_union_Ioc_eq_Ioc
        (he (by omega : n ≤ n + 1)) (he (Nat.zero_le n))]
    rw [hsets, sum_union]
    apply disjoint_left.mpr
    intro p hp hq
    have hpI := mem_Ioc.mp (mem_filter.mp hp).1
    have hqI := mem_Ioc.mp (mem_filter.mp hq).1
    omega

/-- Auxiliary cumulative budget for second memoir page 99 formula 18.3.
The printed block upper masses leave the strict margin 0.02 in each later crude budget. -/

lemma decomp338_cumulative_mass_budget (h : ℕ) (e : ℕ → ℕ) (he : Antitone e)
    (n : ℕ) (hn : 3 ≤ n)
    (hm : ∀ i < n, (∑ p ∈ (Ioc (e (i + 1)) (e i)).filter Nat.Prime, nuN h p) ≤
      (decomp305HeadMass i : ℝ) / 100) :
    (∑ p ∈ (Ioc (e n) (e 0)).filter Nat.Prime, nuN h p) ≤
      (n : ℝ) / 2 + 0.48 := by
  rw [← decomp338_prime_mass_telescopes (nuN h) e he n,
    ← decomp305_head_mass_sum hn]
  apply sum_le_sum
  intro i hi
  exact hm i (mem_range.mp hi)

private def decomp338GreedyStep (h Y w i : ℕ) : ℕ :=
  if H : ∃ y : ℕ, Y ≤ y ∧ y ≤ w ∧
      (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p) ≤ (decomp305HeadMass i : ℝ) / 100
    then Nat.find H else w

/-- Auxiliary decreasing prime cutoffs for second memoir pages 109 to 111.
Apply the greedy endpoint successively at the printed lower block masses. -/

private def decomp338GreedyCutoff (h Y t : ℕ) : ℕ → ℕ
  | 0 => decomp338GreedyStep h Y t 0
  | i + 1 => decomp338GreedyStep h Y (decomp338GreedyCutoff h Y t i) (i + 1)

/-- Auxiliary endpoint bounds for second memoir pages 109 to 111.
A nonempty bounded greedy search stays between its endpoints and obeys the target mass. -/

lemma decomp338_greedy_step_bounds (h Y w i : ℕ) (hYw : Y ≤ w) :
    Y ≤ decomp338GreedyStep h Y w i ∧ decomp338GreedyStep h Y w i ≤ w ∧
      (∑ p ∈ (Ioc (decomp338GreedyStep h Y w i) w).filter Nat.Prime, nuN h p) ≤
        (decomp305HeadMass i : ℝ) / 100 := by
  have hex : ∃ y : ℕ, Y ≤ y ∧ y ≤ w ∧
      (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p) ≤ (decomp305HeadMass i : ℝ) / 100 :=
    ⟨w, hYw, le_rfl, by simpa using (decomp338_head_mass_pos i).le⟩
  unfold decomp338GreedyStep
  rw [dif_pos hex]
  exact Nat.find_spec hex

/-- Auxiliary decreasing endpoint bounds for second memoir pages 109 to 111.
Every greedy cutoff remains above its fixed residual endpoint. -/

lemma decomp338_greedy_cutoff_bounds (h Y t : ℕ) (hYt : Y ≤ t) :
    Antitone (decomp338GreedyCutoff h Y t) ∧
      (∀ i, Y ≤ decomp338GreedyCutoff h Y t i) ∧ decomp338GreedyCutoff h Y t 0 ≤ t := by
  have hlo (i : ℕ) : Y ≤ decomp338GreedyCutoff h Y t i := by
    induction i with
    | zero => exact (decomp338_greedy_step_bounds h Y t 0 hYt).1
    | succ i ih => exact (decomp338_greedy_step_bounds h Y _ (i + 1) ih).1
  refine ⟨antitone_nat_of_succ_le ?_, hlo, (decomp338_greedy_step_bounds h Y t 0 hYt).2.1⟩
  intro i
  exact (decomp338_greedy_step_bounds h Y _ (i + 1) (hlo i)).2.1

lemma decomp338_pair_normalized_tail (h w : ℕ) (heven : Even h)
    (c : ℕ → ℕ) (hc : Antitone c) (hw : c 0 ≤ w) (s n Y : ℕ)
    (hY : 4 ≤ Y) (hbottom : Y ≤ c (s + n))
    (hmass : ∀ i < n,
      (∑ p ∈ (Ioc (c (s + i + 1)) w).filter Nat.Prime, nuN h p) ≤
        (((s + i + 2 : ℕ) : ℝ) + 1) / 2) :
    let E := fun i => ∑ S ∈ decomp305PrimeFamily w c (s + i),
      (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p
    let D := fun i => ∏ p ∈ (Ioc (c (s + i)) w).filter Nat.Prime, (1 - nuN h p)
    E 0 / D 0 - exp (8 / (Y : ℝ)) *
      (∑ i ∈ range n, decomp305CrudeTerm (s + i + 2)) ≤ E n / D n := by
  let E := fun i => ∑ S ∈ decomp305PrimeFamily w c (s + i),
    (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p
  let D := fun i => ∏ p ∈ (Ioc (c (s + i)) w).filter Nat.Prime, (1 - nuN h p)
  let B := fun i => (Ioc (c (s + i + 1)) (c (s + i))).filter Nat.Prime
  let v := fun i => ∏ p ∈ B i, (1 - nuN h p)
  let Φ := fun i => ∑ S ∈ decomp305PrimeFamily w c (s + i),
    (∏ p ∈ S, nuN h p) * LeanLab.PNTSieve.Bonferroni.esymm (nuN h) (B i)
      (2 * (s + i + 1) + 1 - S.card + 1)
  have hD (i : ℕ) : 0 < D i := by
    apply prod_pos
    intro p hp
    exact sub_pos.mpr (nuN_lt_one heven (mem_filter.mp hp).2)
  have hprefix (i : ℕ) : D i = D 0 * ∏ j ∈ range i, v j := by
    simpa [D, v, B] using decomp305_prime_product_iteration (nuN h) w c hc hw s i
  have hraw := decomp305_pair_prime_normalized h w heven c hc hw s n
  change E 0 - (∑ i ∈ range n, Φ i / (∏ j ∈ range (i + 1), v j)) ≤
    E n / (∏ j ∈ range n, v j) at hraw
  have hnorm : E 0 / D 0 - (∑ i ∈ range n, Φ i / D (i + 1)) ≤ E n / D n := by
    calc
      _ = (E 0 - (∑ i ∈ range n, Φ i / (∏ j ∈ range (i + 1), v j))) / D 0 := by
        rw [sub_div]
        congr 1
        rw [sum_div]
        apply sum_congr rfl
        intro i hi
        rw [div_div, mul_comm (∏ j ∈ range (i + 1), v j), ← hprefix (i + 1)]
      _ ≤ (E n / (∏ j ∈ range n, v j)) / D 0 :=
        div_le_div_of_nonneg_right hraw (hD 0).le
      _ = E n / D n := by
        rw [div_div, mul_comm (∏ j ∈ range n, v j), ← hprefix n]
  have hsum : (∑ i ∈ range n, Φ i / D (i + 1)) ≤
      exp (8 / (Y : ℝ)) * ∑ i ∈ range n, decomp305CrudeTerm (s + i + 2) := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    have hin : i < n := mem_range.mp hi
    have hy : Y ≤ c (s + i + 1) := hbottom.trans (hc (by omega : s + i + 1 ≤ s + n))
    have hbound := decomp305_pair_boundary_normalized h w c hc (s + i)
      ((hc (Nat.zero_le _)).trans hw) (by omega) (hmass i hin)
    change Φ i / D (i + 1) ≤ exp (8 / (c (s + i + 1) : ℝ)) *
      decomp305CrudeTerm (s + i + 2) at hbound
    apply hbound.trans
    apply mul_le_mul_of_nonneg_right
    · apply exp_le_exp.mpr
      exact div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast (by omega : 0 < Y))
        (by exact_mod_cast hy)
    · unfold decomp305CrudeTerm
      positivity
  change E 0 / D 0 - exp (8 / (Y : ℝ)) *
    (∑ i ∈ range n, decomp305CrudeTerm (s + i + 2)) ≤ E n / D n
  linarith


/-- Auxiliary summability needed to compare finite actual tails with second memoir page 99 formula 18.3.
The existing consecutive ratio bound gives the complete later shifted factorial tail. -/

lemma decomp338_crude_tail_summable : Summable (fun k : ℕ => decomp305CrudeTerm (21 + k)) := by
  have hpos (b : ℕ) : 0 ≤ decomp305CrudeTerm b := by unfold decomp305CrudeTerm; positivity
  apply summable_of_ratio_norm_eventually_le (r := (0.86 : ℝ)) (by norm_num)
  apply Eventually.of_forall
  intro k
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (hpos (21 + (k + 1))), abs_of_nonneg (hpos (21 + k))]
  simpa only [Nat.add_assoc] using decomp305_crude_ratio (b := 21 + k) (by omega)

/-- Auxiliary positive normalized actual main sum for second memoir page 99 formula 18.3.
A normalized twenty block head at least 0.04 survives the full later crude tail.
The residual endpoint bound one hundred is auxiliary. -/

lemma decomp338_pair_normalized_positive (h w : ℕ) (heven : Even h)
    (c : ℕ → ℕ) (hc : Antitone c) (hw : c 0 ≤ w) (n Y : ℕ)
    (hY : 100 ≤ Y) (hbottom : Y ≤ c (19 + n))
    (hmass : ∀ i < n,
      (∑ p ∈ (Ioc (c (19 + i + 1)) w).filter Nat.Prime, nuN h p) ≤
        (((19 + i + 2 : ℕ) : ℝ) + 1) / 2)
    (hhead : (0.04 : ℝ) ≤
      (∑ S ∈ decomp305PrimeFamily w c 19,
        (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p) /
      (∏ p ∈ (Ioc (c 19) w).filter Nat.Prime, (1 - nuN h p))) :
    (0.02 : ℝ) ≤
      (∑ S ∈ decomp305PrimeFamily w c (19 + n),
        (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p) /
      (∏ p ∈ (Ioc (c (19 + n)) w).filter Nat.Prime, (1 - nuN h p)) := by
  have hraw := decomp338_pair_normalized_tail h w heven c hc hw 19 n Y (by omega) hbottom hmass
  dsimp only at hraw
  have he008 : exp (0.08 : ℝ) ≤ 1.1 := ricci_exp_upper_small
    (by norm_num) (by norm_num) (by norm_num [sum_range_succ, Nat.factorial])
  have he : exp (8 / (Y : ℝ)) ≤ 1.1 := by
    apply le_trans _ he008
    apply exp_le_exp.mpr
    have hYR : (100 : ℝ) ≤ Y := by exact_mod_cast hY
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < Y)]
    linarith
  have htail : (∑ i ∈ range n, decomp305CrudeTerm (19 + i + 2)) < 0.018 := by
    have hh := decomp338_crude_tail_summable.sum_le_tsum (range n)
      (fun i _ => show 0 ≤ decomp305CrudeTerm (21 + i) by unfold decomp305CrudeTerm; positivity)
    have hindex : (∑ i ∈ range n, decomp305CrudeTerm (19 + i + 2)) =
        ∑ i ∈ range n, decomp305CrudeTerm (21 + i) := by
      apply sum_congr rfl
      intro i hi
      congr 1
      omega
    rw [hindex]
    exact hh.trans_lt decomp305_crude_tail_lt
  have htail0 : 0 ≤ ∑ i ∈ range n, decomp305CrudeTerm (19 + i + 2) := by
    apply sum_nonneg
    intro i hi
    unfold decomp305CrudeTerm
    positivity
  have hmul := mul_le_mul he htail.le htail0 (by norm_num : (0 : ℝ) ≤ 1.1)
  norm_num at hmul
  norm_num only [Nat.add_zero] at hraw
  linarith

lemma decomp338_retained_mass_tendsto (h w : ℕ → ℕ) (c : ℕ → ℕ → ℕ)
    (hc : ∀ q, Antitone (c q)) (hw : ∀ q, c q 0 ≤ w q)
    (ht : ∀ i, Tendsto
      (fun q => ∑ p ∈ decomp338PrimeBlock (w q) (c q) i, nuN (h q) p)
      atTop (nhds ((decomp305HeadMass i : ℝ) / 100))) (n : ℕ) :
    Tendsto (fun q => ∑ p ∈ (Ioc (c q n) (w q)).filter Nat.Prime, nuN (h q) p)
      atTop (nhds (∑ i ∈ range (n + 1), (decomp305HeadMass i : ℝ) / 100)) := by
  have heq (q : ℕ) :
      (∑ i ∈ range (n + 1), ∑ p ∈ decomp338PrimeBlock (w q) (c q) i, nuN (h q) p) =
        ∑ p ∈ (Ioc (c q n) (w q)).filter Nat.Prime, nuN (h q) p := by
    let e : ℕ → ℕ := fun i => match i with
      | 0 => w q
      | j + 1 => c q j
    have he : Antitone e := by
      apply antitone_nat_of_succ_le
      intro i
      cases i with
      | zero => exact hw q
      | succ i => exact hc q (by omega : i ≤ i + 1)
    have hh := decomp338_prime_mass_telescopes (nuN (h q)) e he (n + 1)
    calc
      _ = ∑ i ∈ range (n + 1), ∑ p ∈ (Ioc (e (i + 1)) (e i)).filter Nat.Prime,
          nuN (h q) p := by
        apply sum_congr rfl
        intro i hi
        cases i <;> rfl
      _ = _ := hh
  have hh := tendsto_finsetSum (range (n + 1)) (fun i _ => ht i)
  exact hh.congr' (Eventually.of_forall heq)

/-- Auxiliary normalized finite head limit for second memoir pages 99 and 111.
Any actual prime blocks with the printed moment limits have normalized twenty block head eventually above 0.04. -/

lemma decomp338_normalized_head_of_moments (h w : ℕ → ℕ) (c : ℕ → ℕ → ℕ)
    (heven : ∀ q, Even (h q)) (hc : ∀ q, Antitone (c q)) (hw : ∀ q, c q 0 ≤ w q)
    (ht : ∀ i, Tendsto
      (fun q => ∑ p ∈ decomp338PrimeBlock (w q) (c q) i, nuN (h q) p)
      atTop (nhds ((decomp305HeadMass i : ℝ) / 100)))
    (hsq : ∀ i, Tendsto
      (fun q => ∑ p ∈ decomp338PrimeBlock (w q) (c q) i, (nuN (h q) p) ^ 2)
      atTop (nhds 0)) :
    ∀ᶠ q : ℕ in atTop, (0.04 : ℝ) <
      (∑ S ∈ decomp305PrimeFamily (w q) (c q) 19,
        (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN (h q) p) /
      (∏ p ∈ (Ioc (c q 19) (w q)).filter Nat.Prime, (1 - nuN (h q) p)) := by
  let E := fun q => ∑ S ∈ decomp305PrimeFamily (w q) (c q) 19,
    (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN (h q) p
  let M := fun q => ∑ p ∈ (Ioc (c q 19) (w q)).filter Nat.Prime, nuN (h q) p
  let D := fun q => ∏ p ∈ (Ioc (c q 19) (w q)).filter Nat.Prime, (1 - nuN (h q) p)
  have hE := decomp338_prime_head_tendsto (fun q => nuN (h q)) w c hc hw
    (fun q => nuN_nonneg (h q)) ht hsq 19
  change Tendsto E atTop (nhds (decomp305HeadValue 20 : ℝ)) at hE
  have hM : Tendsto M atTop (nhds (10.48 : ℝ)) := by
    have hh := decomp338_retained_mass_tendsto h w c hc hw ht 19
    have hs := decomp305_head_mass_sum (b := 20) (by norm_num)
    norm_num at hs
    change Tendsto M atTop (nhds (∑ i ∈ range 20, (decomp305HeadMass i : ℝ) / 100)) at hh
    rw [hs] at hh
    convert hh using 1 <;> norm_num
  have hD (q : ℕ) : 0 < D q := by
    apply prod_pos
    intro p hp
    exact sub_pos.mpr (nuN_lt_one (heven q) (mem_filter.mp hp).2)
  have hprod (q : ℕ) : D q ≤ exp (-M q) := by
    calc
      _ ≤ ∏ p ∈ (Ioc (c q 19) (w q)).filter Nat.Prime, exp (-nuN (h q) p) := by
        apply prod_le_prod₀
        · intro p hp
          exact (sub_pos.mpr (nuN_lt_one (heven q) (mem_filter.mp hp).2)).le
        · intro p hp
          exact one_sub_le_exp_neg _
      _ = exp (-M q) := by rw [← exp_sum, sum_neg_distrib]
  have hval : (13 / 10000000 : ℝ) < (decomp305HeadValue 20 : ℝ) := by
    have hh : ((13 / 10000000 : ℚ) : ℝ) < (decomp305HeadValue 20 : ℝ) :=
      Rat.cast_lt.mpr decomp305_head20_positive
    norm_num at hh
    exact hh
  have he10 : (2.718 : ℝ) ^ (10 : ℕ) ≤ exp (10 : ℝ) := by
    calc
      _ ≤ exp (1 : ℝ) ^ (10 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) (by linarith [exp_one_gt_d9]) _
      _ = exp (10 : ℝ) := by rw [← exp_nat_mul]; norm_num
  have he048 : (1.48 : ℝ) ≤ exp (0.48 : ℝ) := by linarith [add_one_le_exp (0.48 : ℝ)]
  have he : (31000 : ℝ) ≤ exp (10.48 : ℝ) := by
    calc
      _ ≤ 2.718 ^ (10 : ℕ) * 1.48 := by norm_num
      _ ≤ exp (10 : ℝ) * exp (0.48 : ℝ) :=
        mul_le_mul he10 he048 (by norm_num) (exp_pos _).le
      _ = _ := by rw [← exp_add]; norm_num
  have hmargin : (0.04 : ℝ) < exp (10.48 : ℝ) * (decomp305HeadValue 20 : ℝ) := by
    have hh := mul_le_mul he hval.le (by norm_num : (0 : ℝ) ≤ 13 / 10000000) (exp_pos _).le
    norm_num at hh
    linarith
  have hMexp : Tendsto (fun q => exp (M q)) atTop (nhds (exp (10.48 : ℝ))) :=
    (Real.continuous_exp.tendsto _).comp hM
  have hF := hMexp.mul hE
  have hEpos : ∀ᶠ q : ℕ in atTop, 0 < E q :=
    hE.eventually (eventually_gt_nhds (show (0 : ℝ) < (decomp305HeadValue 20 : ℝ) by linarith))
  filter_upwards [hF.eventually (eventually_gt_nhds hmargin), hEpos] with q hFq hEq
  change (0.04 : ℝ) < E q / D q
  apply lt_of_lt_of_le hFq
  apply (le_div_iff₀ (hD q)).mpr
  have heq : exp (M q) * D q ≤ 1 := by
    calc
      _ ≤ exp (M q) * exp (-M q) := mul_le_mul_of_nonneg_left (hprod q) (exp_pos _).le
      _ = 1 := by rw [← exp_add]; simp
  have hm := mul_le_mul_of_nonneg_left heq hEq.le
  convert hm using 1 <;> ring


/-- Auxiliary normalized actual head construction for second memoir pages 99 and 111.
For every sequence of even gaps there are actual decreasing prime blocks whose
normalized twenty block head is eventually greater than 0.04. This asserts no count. -/

lemma decomp338_greedy_step_tendsto (h w : ℕ → ℕ) (hw : Tendsto w atTop atTop) (Y i : ℕ) :
    Tendsto (fun q => decomp338GreedyStep (h q) Y (w q) i) atTop atTop := by
  apply tendsto_atTop.2
  intro Z
  obtain ⟨W, hW, hmass⟩ := decompJ365_pair_block_mass_unbounded (max Y Z)
    ((decomp305HeadMass i : ℝ) / 100 + 1)
  filter_upwards [hw.eventually (eventually_ge_atTop W)] with q hq
  have hYw : Y ≤ w q := (le_max_left Y Z).trans (hW.trans hq)
  obtain ⟨hlo, hhi, hsmall⟩ := decomp338_greedy_step_bounds (h q) Y (w q) i hYw
  by_contra hbad
  have hZ : decomp338GreedyStep (h q) Y (w q) i ≤ max Y Z := by omega
  have hsub : (Ioc (max Y Z) (w q)).filter Nat.Prime ⊆
      (Ioc (decomp338GreedyStep (h q) Y (w q) i) (w q)).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpI, hpP⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hZ.trans_lt (mem_Ioc.mp hpI).1, (mem_Ioc.mp hpI).2⟩, hpP⟩
  have hle := sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => nuN_nonneg (h q) p)
  have hbig := hmass (h q) (w q) hq
  linarith

/-- Auxiliary canonical cutoff limits for second memoir pages 109 to 111.
Every fixed greedy cutoff depth tends to infinity with the top endpoint, uniformly in varying gaps. -/

lemma decomp338_greedy_cutoff_tendsto (h w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (Y i : ℕ) : Tendsto (fun q => decomp338GreedyCutoff (h q) Y (w q) i) atTop atTop := by
  induction i with
  | zero => exact decomp338_greedy_step_tendsto h w hw Y 0
  | succ i ih =>
    exact decomp338_greedy_step_tendsto h
      (fun q => decomp338GreedyCutoff (h q) Y (w q) i) ih Y (i + 1)

/-- Auxiliary sharp greedy mass deficit for second memoir pages 109 to 111.
At an endpoint strictly above the residual cutoff, the missing mass is less than two over that endpoint. -/

lemma decomp338_greedy_step_mass_lower (h Y w i : ℕ) (hYw : Y ≤ w)
    (hstop : Y < decomp338GreedyStep h Y w i) :
    (decomp305HeadMass i : ℝ) / 100 - 2 / (decomp338GreedyStep h Y w i : ℝ) <
      ∑ p ∈ (Ioc (decomp338GreedyStep h Y w i) w).filter Nat.Prime, nuN h p := by
  let y := decomp338GreedyStep h Y w i
  have hex : ∃ z : ℕ, Y ≤ z ∧ z ≤ w ∧
      (∑ p ∈ (Ioc z w).filter Nat.Prime, nuN h p) ≤ (decomp305HeadMass i : ℝ) / 100 :=
    ⟨w, hYw, le_rfl, by simpa using (decomp338_head_mass_pos i).le⟩
  have hy : y = Nat.find hex := by simp only [y, decomp338GreedyStep, dif_pos hex]
  have hyw : y ≤ w := (decomp338_greedy_step_bounds h Y w i hYw).2.1
  have hy0 : 0 < y := by dsimp [y]; omega
  have hprev : (decomp305HeadMass i : ℝ) / 100 <
      ∑ p ∈ (Ioc (y - 1) w).filter Nat.Prime, nuN h p := by
    have hmin := Nat.find_min hex (show y - 1 < Nat.find hex by rw [← hy]; omega)
    apply lt_of_not_ge
    intro hle
    exact hmin ⟨by dsimp [y] at *; omega, by omega, hle⟩
  have hsets : Ioc (y - 1) w = insert y (Ioc y w) := by
    ext p
    simp only [mem_Ioc, mem_insert]
    omega
  have hstep : (∑ p ∈ (Ioc (y - 1) w).filter Nat.Prime, nuN h p) ≤
      (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p) + 2 / (y : ℝ) := by
    rw [hsets, filter_insert]
    by_cases hp : y.Prime
    · rw [ite_eq_left hp, sum_insert (by simp)]
      rw [nuN_prime hp]
      have hh := div_le_div_of_nonneg_right (wt_le_two h y) (by positivity : (0 : ℝ) ≤ y)
      linarith
    · rw [ite_eq_right hp]
      exact le_add_of_nonneg_right (by positivity)
  change (decomp305HeadMass i : ℝ) / 100 - 2 / (y : ℝ) < _
  linarith


/-- Auxiliary total endpoint monotonicity for second memoir pages 109 to 111.
The fallback also stays below the supplied top endpoint. -/

lemma decomp338_greedy_step_le (h Y w i : ℕ) : decomp338GreedyStep h Y w i ≤ w := by
  unfold decomp338GreedyStep
  split_ifs with H
  · exact (Nat.find_spec H).2.1
  · rfl

/-- Auxiliary canonical greedy block mass limit for second memoir page 111 formula 28.8.
The exact endpoint deficit tends to zero with the greedy endpoint. -/

lemma decomp338_greedy_step_mass_tendsto (h w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (Y i : ℕ) :
    Tendsto (fun q => ∑ p ∈ (Ioc (decomp338GreedyStep (h q) Y (w q) i) (w q)).filter Nat.Prime,
      nuN (h q) p) atTop (nhds ((decomp305HeadMass i : ℝ) / 100)) := by
  let y := fun q => decomp338GreedyStep (h q) Y (w q) i
  have hy : Tendsto y atTop atTop := decomp338_greedy_step_tendsto h w hw Y i
  have hyR : Tendsto (fun q => (y q : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hy
  have hinv : Tendsto (fun q => (y q : ℝ)⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero.comp hyR
  have herr : Tendsto (fun q => 2 / (y q : ℝ)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hinv.const_mul 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using tendsto_const_nhds.sub herr) tendsto_const_nhds
  · filter_upwards [hw.eventually (eventually_ge_atTop Y),
      hy.eventually (eventually_ge_atTop (Y + 1))] with q hwq hyq
    change Y + 1 ≤ decomp338GreedyStep (h q) Y (w q) i at hyq
    exact (decomp338_greedy_step_mass_lower (h q) Y (w q) i hwq (by omega)).le
  · filter_upwards [hw.eventually (eventually_ge_atTop Y)] with q hwq
    exact (decomp338_greedy_step_bounds (h q) Y (w q) i hwq).2.2

/-- Auxiliary canonical greedy square mass limit for second memoir page 111 formula 28.9.
A vanishing maximal density and bounded total mass force the square mass to vanish. -/

lemma decomp338_greedy_step_square_tendsto (h w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (Y i : ℕ) :
    Tendsto (fun q => ∑ p ∈ (Ioc (decomp338GreedyStep (h q) Y (w q) i) (w q)).filter Nat.Prime,
      (nuN (h q) p) ^ 2) atTop (nhds 0) := by
  let y := fun q => decomp338GreedyStep (h q) Y (w q) i
  have hy : Tendsto y atTop atTop := decomp338_greedy_step_tendsto h w hw Y i
  have hyR : Tendsto (fun q => (y q : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hy
  have hinv : Tendsto (fun q => (y q : ℝ)⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero.comp hyR
  have hbound : Tendsto (fun q => 2 / (y q : ℝ) * ((decomp305HeadMass i : ℝ) / 100))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (hinv.const_mul 2).mul_const ((decomp305HeadMass i : ℝ) / 100)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
  · exact Eventually.of_forall fun q => sum_nonneg (fun p _ => sq_nonneg _)
  · filter_upwards [hw.eventually (eventually_ge_atTop Y),
      hy.eventually (eventually_ge_atTop 1)] with q hwq hyq
    have hupper := decompJ365_pair_block_square_upper (h q) (y q) (w q) (by omega)
    exact hupper.trans (mul_le_mul_of_nonneg_left
      (decomp338_greedy_step_bounds (h q) Y (w q) i hwq).2.2 (by positivity))

/-- Auxiliary canonical greedy moments for second memoir page 111 formulas 28.8 and 28.9.
At every fixed depth the actual greedy blocks have the printed mass and zero square mass in the limit. -/

lemma decomp338_greedy_block_moments (h w : ℕ → ℕ) (hw : Tendsto w atTop atTop) (Y : ℕ) :
    (∀ i, Tendsto
      (fun q => ∑ p ∈ decomp338PrimeBlock (w q) (decomp338GreedyCutoff (h q) Y (w q)) i,
        nuN (h q) p) atTop (nhds ((decomp305HeadMass i : ℝ) / 100))) ∧
    (∀ i, Tendsto
      (fun q => ∑ p ∈ decomp338PrimeBlock (w q) (decomp338GreedyCutoff (h q) Y (w q)) i,
        (nuN (h q) p) ^ 2) atTop (nhds 0)) := by
  constructor
  · intro i
    cases i with
    | zero => exact decomp338_greedy_step_mass_tendsto h w hw Y 0
    | succ i =>
      exact decomp338_greedy_step_mass_tendsto h
        (fun q => decomp338GreedyCutoff (h q) Y (w q) i)
        (decomp338_greedy_cutoff_tendsto h w hw Y i) Y (i + 1)
  · intro i
    cases i with
    | zero => exact decomp338_greedy_step_square_tendsto h w hw Y 0
    | succ i =>
      exact decomp338_greedy_step_square_tendsto h
        (fun q => decomp338GreedyCutoff (h q) Y (w q) i)
        (decomp338_greedy_cutoff_tendsto h w hw Y i) Y (i + 1)


/-- Auxiliary canonical normalized head for second memoir pages 99 and 111.
For every varying even gap and every top endpoint tending to infinity, the actual
greedy twenty block head divided by its density product is eventually above 0.04. -/

lemma decomp338_greedy_normalized_head (h w : ℕ → ℕ) (heven : ∀ q, Even (h q))
    (hw : Tendsto w atTop atTop) (Y : ℕ) :
    ∀ᶠ q : ℕ in atTop, (0.04 : ℝ) <
      (∑ S ∈ decomp305PrimeFamily (w q) (decomp338GreedyCutoff (h q) Y (w q)) 19,
        (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN (h q) p) /
      (∏ p ∈ (Ioc (decomp338GreedyCutoff (h q) Y (w q) 19) (w q)).filter Nat.Prime,
        (1 - nuN (h q) p)) := by
  let c := fun q => decomp338GreedyCutoff (h q) Y (w q)
  have hc : ∀ q, Antitone (c q) := by
    intro q
    apply antitone_nat_of_succ_le
    intro i
    exact decomp338_greedy_step_le (h q) Y (c q i) (i + 1)
  have hcw : ∀ q, c q 0 ≤ w q := fun q => decomp338_greedy_step_le (h q) Y (w q) 0
  obtain ⟨ht, hsq⟩ := decomp338_greedy_block_moments h w hw Y
  exact decomp338_normalized_head_of_moments h w c heven hc hcw ht hsq

lemma decomp338_greedy_head_uniform (Y : ℕ) :
    ∃ T : ℕ, ∀ h t : ℕ, Even h → T ≤ t → (0.04 : ℝ) ≤
      (∑ S ∈ decomp305PrimeFamily t (decomp338GreedyCutoff h Y t) 19,
        (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p) /
      (∏ p ∈ (Ioc (decomp338GreedyCutoff h Y t 19) t).filter Nat.Prime, (1 - nuN h p)) := by
  by_contra hbad
  push_neg at hbad
  choose h t heven hge hfail using hbad
  have ht : Tendsto t atTop atTop := tendsto_atTop_mono hge tendsto_id
  have hh := decomp338_greedy_normalized_head h t heven ht Y
  obtain ⟨N, hN⟩ := eventually_atTop.mp hh
  have hhN := hN N le_rfl
  have hfN := hfail N
  linarith

/-- Auxiliary canonical cumulative mass budget for second memoir pages 99 and 109.
The printed greedy block upper masses imply the exact cumulative printed budget. -/

lemma decomp338_greedy_cumulative_budget (h Y t : ℕ) (hYt : Y ≤ t) (n : ℕ) (hn : 2 ≤ n) :
    (∑ p ∈ (Ioc (decomp338GreedyCutoff h Y t n) t).filter Nat.Prime, nuN h p) ≤
      ((n + 1 : ℕ) : ℝ) / 2 + 0.48 := by
  let c := decomp338GreedyCutoff h Y t
  obtain ⟨hc, hlo, hw⟩ := decomp338_greedy_cutoff_bounds h Y t hYt
  let e : ℕ → ℕ := fun i => match i with
    | 0 => t
    | j + 1 => c j
  have he : Antitone e := by
    apply antitone_nat_of_succ_le
    intro i
    cases i with
    | zero => exact hw
    | succ i => exact hc (by omega : i ≤ i + 1)
  apply decomp338_cumulative_mass_budget h e he (n + 1) (by omega)
  intro i hi
  cases i with
  | zero => exact (decomp338_greedy_step_bounds h Y t 0 hYt).2.2
  | succ i => exact (decomp338_greedy_step_bounds h Y (c i) (i + 1) (hlo i)).2.2

/-- Supply proof of the finite positive main sum piece.
Second memoir page 99 formula 18.3, page 111 formula 28.11 and page 112 formula 30.2.
This is a density statement and contains no integer count. -/

theorem decomp338_greedy_main_proved :
    ∃ Y₀ : ℕ, 4 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ a : ℝ, 0 < a ∧ ∃ T : ℕ, ∀ h t : ℕ, Even h → T ≤ t →
        a * (∏ p ∈ Nat.primesLE t, (1 - nuN h p)) ≤
          ∑ S ∈ (Nat.primesLE t).powerset.filter (fun S =>
            ∀ j ∈ range (t + 1),
              (S.filter (fun p => decomp338GreedyCutoff h Y t j < p)).card ≤ 2 * j + 1),
            (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p := by
  refine ⟨100, by norm_num, ?_⟩
  intro Y hY
  obtain ⟨T, hT⟩ := decomp338_greedy_head_uniform Y
  refine ⟨0.02, by norm_num, max T (max Y 19), ?_⟩
  intro h t heven ht
  have hYt : Y ≤ t := by omega
  have ht19 : 19 ≤ t := by omega
  let c := decomp338GreedyCutoff h Y t
  obtain ⟨hc, hlo, hw⟩ := decomp338_greedy_cutoff_bounds h Y t hYt
  have hmass : ∀ i < t - 19,
      (∑ p ∈ (Ioc (c (19 + i + 1)) t).filter Nat.Prime, nuN h p) ≤
        (((19 + i + 2 : ℕ) : ℝ) + 1) / 2 := by
    intro i hi
    have hh := decomp338_greedy_cumulative_budget h Y t hYt (19 + i + 1) (by omega)
    have heq : (19 + i + 1 + 1 : ℕ) = 19 + i + 2 := by omega
    rw [heq] at hh
    change (∑ p ∈ (Ioc (c (19 + i + 1)) t).filter Nat.Prime, nuN h p) ≤ _ at hh
    linarith
  have hhead := hT h t heven (by omega)
  have hpos := decomp338_pair_normalized_positive h t heven c hc hw (t - 19) Y hY
    (hlo (19 + (t - 19))) hmass hhead
  rw [show 19 + (t - 19) = t by omega] at hpos
  let E := ∑ S ∈ decomp305PrimeFamily t c t, (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p
  let D := ∏ p ∈ (Ioc (c t) t).filter Nat.Prime, (1 - nuN h p)
  let z := ∏ p ∈ Nat.primesLE (c t), (1 - nuN h p)
  have hD : 0 < D := by
    apply prod_pos
    intro p hp
    exact sub_pos.mpr (nuN_lt_one heven (mem_filter.mp hp).2)
  change (0.02 : ℝ) ≤ E / D at hpos
  have hmul := mul_le_mul_of_nonneg_right ((le_div_iff₀ hD).mp hpos)
    (show 0 ≤ z from prod_nonneg (fun p hp =>
      (sub_pos.mpr (nuN_lt_one heven (Nat.mem_primesLE.mp hp).2)).le))
  have hct : c t ≤ t := (hc (Nat.zero_le t)).trans hw
  have hcomplete := decomp305_prime_family_complete (nuN h) t c hc t hct
  change (∑ S ∈ (Nat.primesLE t).powerset.filter (fun S =>
    ∀ j ∈ range (t + 1), (S.filter (fun p => c j < p)).card ≤ 2 * j + 1),
      (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p) = E * z at hcomplete
  have hsets : Nat.primesLE t = (Ioc (c t) t).filter Nat.Prime ∪ Nat.primesLE (c t) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpt, hprime⟩ := Nat.mem_primesLE.mp hp
      by_cases hpc : p ≤ c t
      · exact mem_union.mpr (Or.inr (Nat.mem_primesLE.mpr ⟨hpc, hprime⟩))
      · exact mem_union.mpr (Or.inl (mem_filter.mpr
          ⟨mem_Ioc.mpr ⟨by omega, hpt⟩, hprime⟩))
    · intro hp
      rcases mem_union.mp hp with hp | hp
      · obtain ⟨hpI, hprime⟩ := mem_filter.mp hp
        exact Nat.mem_primesLE.mpr ⟨(mem_Ioc.mp hpI).2, hprime⟩
      · obtain ⟨hpc, hprime⟩ := Nat.mem_primesLE.mp hp
        exact Nat.mem_primesLE.mpr ⟨hpc.trans hct, hprime⟩
  have hdisj : Disjoint ((Ioc (c t) t).filter Nat.Prime) (Nat.primesLE (c t)) := by
    apply disjoint_left.mpr
    intro p hp hq
    have hp' := (mem_Ioc.mp (mem_filter.mp hp).1).1
    have hq' := (Nat.mem_primesLE.mp hq).1
    omega
  have hprod : (∏ p ∈ Nat.primesLE t, (1 - nuN h p)) = D * z := by
    rw [hsets, prod_union hdisj]
  rw [hcomplete, hprod]
  nlinarith

lemma decomp338_head_mass_ge_half (i : ℕ) : (1 / 2 : ℝ) ≤ (decomp305HeadMass i : ℝ) / 100 := by
  rcases i with _ | i
  · norm_num [decomp305HeadMass]
  rcases i with _ | i
  · norm_num [decomp305HeadMass]
  rcases i with _ | i
  · norm_num [decomp305HeadMass]
  · norm_num [decomp305HeadMass]

/-- Auxiliary strict greedy descent for second memoir pages 109 to 111.
Above a residual endpoint at least four, the next greedy endpoint strictly decreases. -/

lemma decomp338_greedy_step_lt (h Y w i : ℕ) (hY : 4 ≤ Y) (hYw : Y < w) :
    decomp338GreedyStep h Y w i < w := by
  have hw0 : 0 < w := by omega
  have hset : Ioc (w - 1) w = ({w} : Finset ℕ) := by
    ext p
    simp only [mem_Ioc, mem_singleton]
    omega
  have hmass : (∑ p ∈ (Ioc (w - 1) w).filter Nat.Prime, nuN h p) ≤
      (decomp305HeadMass i : ℝ) / 100 := by
    apply le_trans _ (decomp338_head_mass_ge_half i)
    rw [hset]
    by_cases hp : w.Prime
    · simp only [filter_singleton, hp, ite_true, sum_singleton]
      rw [nuN_prime hp]
      have hwR : (4 : ℝ) ≤ w := by exact_mod_cast (by omega : 4 ≤ w)
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < w)]
      linarith [wt_le_two h w]
    · simp [filter_singleton, hp]
  have hex : ∃ y : ℕ, Y ≤ y ∧ y ≤ w ∧
      (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p) ≤ (decomp305HeadMass i : ℝ) / 100 :=
    ⟨w, by omega, le_rfl, by simpa using (decomp338_head_mass_pos i).le⟩
  unfold decomp338GreedyStep
  rw [dif_pos hex]
  have hh := Nat.find_min' hex (show Y ≤ w - 1 ∧ w - 1 ≤ w ∧
      (∑ p ∈ (Ioc (w - 1) w).filter Nat.Prime, nuN h p) ≤
        (decomp305HeadMass i : ℝ) / 100 from ⟨by omega, by omega, hmass⟩)
  omega

/-- Auxiliary termination of the canonical greedy cutoffs for second memoir pages 109 to 111.
Depth t has reached the fixed residual endpoint when the top is t. -/

lemma decomp338_greedy_stops (h Y t : ℕ) (hY : 4 ≤ Y) (hYt : Y ≤ t) :
    decomp338GreedyCutoff h Y t t = Y := by
  let c := decomp338GreedyCutoff h Y t
  obtain ⟨hc, hlo, hw⟩ := decomp338_greedy_cutoff_bounds h Y t hYt
  have hbound (i : ℕ) : c i ≤ max Y (t - i) := by
    induction i with
    | zero => exact hw.trans (le_max_right _ _)
    | succ i ih =>
      by_cases hci : c i ≤ Y
      · exact (hc (by omega : i ≤ i + 1)).trans (hci.trans (le_max_left _ _))
      · have hnext : c (i + 1) < c i := decomp338_greedy_step_lt h Y (c i) (i + 1) hY (by omega)
        have hprev : c i ≤ t - i := by omega
        have hh : c (i + 1) ≤ t - (i + 1) := by omega
        exact hh.trans (le_max_right _ _)
  have hh := hbound t
  simp only [Nat.sub_self, max_eq_left (Nat.zero_le Y)] at hh
  exact Nat.le_antisymm hh (hlo t)

/-- Auxiliary uniform endpoint error threshold for second memoir page 109.
Both the greedy mass deficit and the logarithmic endpoint loss are arbitrarily small above one threshold. -/

lemma decomp338_endpoint_error_threshold (ε : ℝ) (hε : 0 < ε) :
    ∃ Y : ℕ, 4 ≤ Y ∧ ∀ y : ℕ, Y ≤ y →
      2 / (y : ℝ) ≤ ε ∧ 28 / Real.log y ≤ ε := by
  have hcast : Tendsto (fun y : ℕ => (y : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun y : ℕ => (y : ℝ)⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero.comp hcast
  have h2 : Tendsto (fun y : ℕ => 2 / (y : ℝ)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hinv.const_mul 2
  have hlog : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop := Real.tendsto_log_atTop.comp hcast
  have hloginv : Tendsto (fun y : ℕ => (Real.log (y : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have h28 : Tendsto (fun y : ℕ => 28 / Real.log y) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hloginv.const_mul 28
  obtain ⟨Y, hY⟩ := eventually_atTop.mp
    (((h2.eventually (eventually_lt_nhds hε)).and
      (h28.eventually (eventually_lt_nhds hε))).and (eventually_ge_atTop 4))
  exact ⟨Y, (hY Y le_rfl).2, fun y hy => ⟨(hY y hy).1.1.le, (hY y hy).1.2.le⟩⟩

/-- Auxiliary endpoint power bound for second memoir page 109 and pages 113 to 114.
Each greedy step lies below the larger of the residual endpoint and its prescribed cutoff power. -/

lemma decomp338_greedy_step_power_max (h Y w i : ℕ) (hY : 4 ≤ Y) (hYw : Y ≤ w)
    (ε : ℝ) (hsmall : ∀ y : ℕ, Y ≤ y → 2 / (y : ℝ) ≤ ε ∧ 28 / Real.log y ≤ ε) :
    (decomp338GreedyStep h Y w i : ℝ) ≤
      max (Y : ℝ) ((w : ℝ) ^ exp (-(decomp305HeadMass i : ℝ) / 100 / 2 + ε)) := by
  let y := decomp338GreedyStep h Y w i
  obtain ⟨hyY, hyw, hmass⟩ := decomp338_greedy_step_bounds h Y w i hYw
  by_cases heq : y = Y
  · rw [show decomp338GreedyStep h Y w i = Y from heq]
    exact le_max_left _ _
  · have hyY' : Y < y := by dsimp [y] at *; omega
    have hm := decomp338_greedy_step_mass_lower h Y w i hYw hyY'
    have herrors := hsmall y hyY
    have hlow : (decomp305HeadMass i : ℝ) / 100 - ε ≤
        ∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p := by
      change (decomp305HeadMass i : ℝ) / 100 - 2 / (y : ℝ) < _ at hm
      linarith
    have hp := decompJ365_pair_block_cutoff_upper h y w
      ((decomp305HeadMass i : ℝ) / 100) ε (by omega) hyw hlow herrors.2
    have he : -((decomp305HeadMass i : ℝ) / 100) / 2 + ε =
        -(decomp305HeadMass i : ℝ) / 100 / 2 + ε := by ring
    rw [he] at hp
    exact hp.trans (le_max_right _ _)

lemma decomp338_support_profile_recurrence (ε : ℝ) (α : ℕ → ℝ)
    (hα1 : α 1 = exp (-0.90 / 2 + ε))
    (hα2 : α 2 = exp (-1.46 / 2 + 2 * ε))
    (htail : ∀ i, α (i + 3) = exp (-1.98 / 2 + 3 * ε) * exp (-0.50 / 2 + ε) ^ i) :
    α 1 = exp (-(decomp305HeadMass 0 : ℝ) / 100 / 2 + ε) ∧
      ∀ i, α (i + 2) = α (i + 1) * exp (-(decomp305HeadMass (i + 1) : ℝ) / 100 / 2 + ε) := by
  constructor
  · rw [hα1]
    congr 1
    norm_num [decomp305HeadMass]
  · intro i
    rcases i with _ | i
    · norm_num only [Nat.zero_add, decomp305HeadMass, Nat.cast_ofNat]
      rw [hα2, hα1, ← exp_add]
      congr 1
      ring
    rcases i with _ | i
    · have h3 : α 3 = exp (-1.98 / 2 + 3 * ε) := by simpa using htail 0
      norm_num only [Nat.zero_add, decomp305HeadMass, Nat.cast_ofNat]
      rw [h3, hα2, ← exp_add]
      congr 1
      ring
    · change α (i + 4) = α (i + 3) * exp (-(decomp305HeadMass (i + 3) : ℝ) / 100 / 2 + ε)
      rw [show i + 4 = (i + 1) + 3 by omega, htail (i + 1), htail i, pow_succ]
      norm_num [decomp305HeadMass] <;> ring

/-- Auxiliary actual cutoff profile for second memoir pages 113 and 114 formulas 31.3 to 31.5.
The canonical greedy cutoffs obey the printed perturbed cumulative powers until the residual endpoint,
and the residual endpoint bounds every later cutoff. -/

lemma decomp338_greedy_profile_bound (h Y t : ℕ) (hY : 4 ≤ Y) (hYt : Y ≤ t)
    (ε : ℝ) (α : ℕ → ℝ)
    (hsmall : ∀ y : ℕ, Y ≤ y → 2 / (y : ℝ) ≤ ε ∧ 28 / Real.log y ≤ ε)
    (hα1 : α 1 = exp (-(decomp305HeadMass 0 : ℝ) / 100 / 2 + ε))
    (hrec : ∀ i, α (i + 2) = α (i + 1) * exp (-(decomp305HeadMass (i + 1) : ℝ) / 100 / 2 + ε))
    (i : ℕ) :
    (decomp338GreedyCutoff h Y t i : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α (i + 1))) := by
  let c := decomp338GreedyCutoff h Y t
  have hlo := (decomp338_greedy_cutoff_bounds h Y t hYt).2.1
  induction i with
  | zero =>
    change (decomp338GreedyStep h Y t 0 : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α 1))
    rw [hα1]
    exact decomp338_greedy_step_power_max h Y t 0 hY hYt ε hsmall
  | succ i ih =>
    change (c (i + 1) : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α (i + 2)))
    change (c i : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α (i + 1))) at ih
    by_cases hp : (t : ℝ) ^ (α (i + 1)) ≤ Y
    · have hci : (c i : ℝ) ≤ Y := by simpa only [max_eq_left hp] using ih
      have hs : (c (i + 1) : ℝ) ≤ c i := by
        exact_mod_cast decomp338_greedy_step_le h Y (c i) (i + 1)
      exact hs.trans (hci.trans (le_max_left _ _))
    · have hci : (c i : ℝ) ≤ (t : ℝ) ^ (α (i + 1)) := by
        simpa only [max_eq_right (le_of_lt (lt_of_not_ge hp))] using ih
      let r := exp (-(decomp305HeadMass (i + 1) : ℝ) / 100 / 2 + ε)
      have hstep := decomp338_greedy_step_power_max h Y (c i) (i + 1) hY (hlo i) ε hsmall
      change (c (i + 1) : ℝ) ≤ max (Y : ℝ) ((c i : ℝ) ^ r) at hstep
      have hrpow : (c i : ℝ) ^ r ≤ ((t : ℝ) ^ (α (i + 1))) ^ r :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hci (exp_pos _).le
      have heq : ((t : ℝ) ^ (α (i + 1))) ^ r = (t : ℝ) ^ (α (i + 2)) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg _), hrec i]
      have hle : (c i : ℝ) ^ r ≤ (t : ℝ) ^ (α (i + 2)) := hrpow.trans_eq heq
      exact hstep.trans (max_le_max_left _ hle)

theorem decomp338_greedy_support_proved :
    ∃ Y₀ : ℕ, 4 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ δ κ : ℝ, 1 / 7 < δ ∧ δ ≤ 1 / 2 ∧ 0 < κ ∧
        ∃ X : ℕ, ∀ ξ h : ℕ, X ≤ ξ →
          let t := ⌊(ξ : ℝ) ^ δ⌋₊
          ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
            (S.filter (fun p => decomp338GreedyCutoff h Y t j < p)).card ≤ 2 * j + 1) →
              ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (ξ : ℝ) ^ (1 - κ) := by
  obtain ⟨ε, α, δ, κ, hε0, hε, hδ0, hκ, hδ7, hα1, hα2, htail, hsave⟩ :=
    decompJ365_first_case_support_parameters
  obtain ⟨Y₀, hY₀, hsmall₀⟩ := decomp338_endpoint_error_threshold ε hε0
  obtain ⟨hfirst, hrec⟩ := decomp338_support_profile_recurrence ε α hα1 hα2 htail
  refine ⟨Y₀, hY₀, ?_⟩
  intro Y hY
  let δ' := min δ (1 / 2)
  have hδ' : 1 / 7 < δ' := lt_min hδ7 (by norm_num)
  have hδ'0 : 0 < δ' := by linarith
  refine ⟨δ', κ / 2, hδ', min_le_right _ _, by positivity, ?_⟩
  let C : ℕ := ∏ p ∈ Nat.primesLE Y, p
  have hCpos : 0 < C := by
    apply prod_pos
    intro p hp
    exact (Nat.mem_primesLE.mp hp).2.pos
  have hcast : Tendsto (fun ξ : ℕ => (ξ : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hδ'0).comp hcast).eventually
      (eventually_ge_atTop ((max Y 2 : ℕ) : ℝ)))
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (show 0 < κ / 2 by positivity)).comp hcast).eventually
      (eventually_ge_atTop (C : ℝ)))
  refine ⟨max 2 (max X₁ X₂), ?_⟩
  intro ξ h hξ
  dsimp only
  let t := ⌊(ξ : ℝ) ^ δ'⌋₊
  intro S hS hcaps
  change S ⊆ Nat.primesLE t at hS
  change ∀ j ∈ range (t + 1),
    (S.filter (fun p : ℕ => decomp338GreedyCutoff h Y t j < p)).card ≤ 2 * j + 1 at hcaps
  have hξ2 : 2 ≤ ξ := by omega
  have hξ0 : (0 : ℝ) < ξ := by exact_mod_cast (by omega : 0 < ξ)
  have hξ1 : (1 : ℝ) ≤ ξ := by exact_mod_cast (by omega : 1 ≤ ξ)
  have htm : max Y 2 ≤ t := Nat.le_floor (hX₁ ξ (by omega))
  have hYt : Y ≤ t := by omega
  have hY4 : 4 ≤ Y := hY₀.trans hY
  have ht2 : 2 ≤ t := by omega
  have hsmall : ∀ y : ℕ, Y ≤ y → 2 / (y : ℝ) ≤ ε ∧ 28 / Real.log y ≤ ε :=
    fun y hy => hsmall₀ y (hY.trans hy)
  have hprofile := decomp338_greedy_profile_bound h Y t hY4 hYt ε α hsmall hfirst hrec
  have hstop := decomp338_greedy_stops h Y t hY4 hYt
  let A := S.filter (fun p => Y < p)
  let B := S.filter (fun p => p ≤ Y)
  have hAB : S = A ∪ B := by
    ext p
    simp only [A, B, mem_filter, mem_union]
    constructor
    · intro hp
      by_cases hy : Y < p
      · exact Or.inl ⟨hp, hy⟩
      · exact Or.inr ⟨hp, by omega⟩
    · intro hp
      rcases hp with hp | hp <;> exact hp.1
  have hdisj : Disjoint A B := by
    apply disjoint_left.mpr
    intro p hp hq
    have hpY := (mem_filter.mp hp).2
    have hqY := (mem_filter.mp hq).2
    omega
  have hBsub : B ⊆ Nat.primesLE Y := by
    intro p hp
    obtain ⟨hpS, hpY⟩ := mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpY, (Nat.mem_primesLE.mp (hS hpS)).2⟩
  have hBbound : (∏ p ∈ B, p) ≤ C :=
    Nat.le_of_dvd hCpos (prod_dvd_prod_of_subset B (Nat.primesLE Y) id hBsub)
  have hcard : A.card ≤ 2 * t + 1 := by
    have hh := hcaps t (mem_range.mpr (by omega : t < t + 1))
    simpa only [hstop] using hh
  have hAcaps : ∀ i ∈ range t,
      (A.filter (fun p : ℕ => (t : ℝ) ^ (α (i + 1)) < (p : ℝ))).card ≤ 2 * i + 1 := by
    intro i hi
    have hsub : A.filter (fun p : ℕ => (t : ℝ) ^ (α (i + 1)) < (p : ℝ)) ⊆
        S.filter (fun p : ℕ => decomp338GreedyCutoff h Y t i < p) := by
      intro p hp
      obtain ⟨hpA, hpow⟩ := mem_filter.mp hp
      obtain ⟨hpS, hpY⟩ := mem_filter.mp hpA
      have hpYR : (Y : ℝ) < p := by exact_mod_cast hpY
      have hmax : max (Y : ℝ) ((t : ℝ) ^ (α (i + 1))) < p := max_lt_iff.mpr ⟨hpYR, hpow⟩
      have hcR := (hprofile i).trans_lt hmax
      exact mem_filter.mpr ⟨hpS, by exact_mod_cast hcR⟩
    exact (card_le_card hsub).trans (hcaps i (mem_range.mpr (by have := mem_range.mp hi; omega)))
  have htop : (t : ℝ) ≤ (ξ : ℝ) ^ δ := by
    calc
      _ ≤ (ξ : ℝ) ^ δ' := Nat.floor_le (by positivity)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hξ1 (min_le_left _ _)
  have hApos : ∀ p ∈ A, 0 < p := by
    intro p hp
    exact (Nat.mem_primesLE.mp (hS (mem_filter.mp hp).1)).2.pos
  have hAmax : ∀ p ∈ A, (p : ℝ) ≤ t := by
    intro p hp
    exact_mod_cast (Nat.mem_primesLE.mp (hS (mem_filter.mp hp).1)).1
  have hlarge := hsave t A ξ t hξ1 (by exact_mod_cast (by omega : 1 < t))
    htop hApos hAmax hcard hAcaps
  have hsmallprod : ((∏ p ∈ B, p : ℕ) : ℝ) ≤ C := by exact_mod_cast hBbound
  have hCbound : (C : ℝ) ≤ (ξ : ℝ) ^ (κ / 2) := hX₂ ξ (by omega)
  have hsplit : ((∏ p ∈ S, p : ℕ) : ℝ) =
      ((∏ p ∈ A, p : ℕ) : ℝ) * ((∏ p ∈ B, p : ℕ) : ℝ) := by
    rw [hAB, prod_union hdisj, Nat.cast_mul]
  calc
    _ = ((∏ p ∈ A, p : ℕ) : ℝ) * ((∏ p ∈ B, p : ℕ) : ℝ) := hsplit
    _ ≤ (ξ : ℝ) ^ (1 - κ) * (C : ℝ) :=
      mul_le_mul hlarge hsmallprod (Nat.cast_nonneg _) (Real.rpow_nonneg hξ0.le _)
    _ ≤ (ξ : ℝ) ^ (1 - κ) * (ξ : ℝ) ^ (κ / 2) :=
      mul_le_mul_of_nonneg_left hCbound (Real.rpow_nonneg hξ0.le _)
    _ = (ξ : ℝ) ^ (1 - κ / 2) := by
      rw [← Real.rpow_add hξ0]
      congr 1
      ring

theorem decomp338_greedy_main :
    ∃ Y₀ : ℕ, 4 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ a : ℝ, 0 < a ∧ ∃ T : ℕ, ∀ h t : ℕ, Even h → T ≤ t →
        a * (∏ p ∈ Nat.primesLE t, (1 - nuN h p)) ≤
          ∑ S ∈ (Nat.primesLE t).powerset.filter (fun S =>
            ∀ j ∈ range (t + 1),
              (S.filter (fun p => decomp338GreedyCutoff h Y t j < p)).card ≤ 2 * j + 1),
            (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p := by
  exact decomp338_greedy_main_proved

/-- LEAF. Second memoir pages 113 and 114 formulas 31.3 to 31.5,
auxiliary saved support for the first pair on first memoir page 89.
This bounds only retained prime products and contains no integer count. -/

theorem decomp338_greedy_support :
    ∃ Y₀ : ℕ, 4 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ δ κ : ℝ, 1 / 7 < δ ∧ δ ≤ 1 / 2 ∧ 0 < κ ∧
        ∃ X : ℕ, ∀ ξ h : ℕ, X ≤ ξ →
          let t := ⌊(ξ : ℝ) ^ δ⌋₊
          ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
            (S.filter (fun p => decomp338GreedyCutoff h Y t j < p)).card ≤ 2 * j + 1) →
              ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (ξ : ℝ) ^ (1 - κ) := by
  exact decomp338_greedy_support_proved


/-- Auxiliary full pair density lower bound for first memoir page 88.
The exceptional prime two contributes exactly one half for an even gap. -/

lemma decomp338_full_pair_product_lower (h t : ℕ) (hh : Even h) (ht : 3 ≤ t) :
    exp (-52 : ℝ) / (2 * Real.log t ^ 2) ≤
      ∏ p ∈ Nat.primesLE t, (1 - nuN h p) := by
  let P := (Nat.primesLE t).erase 2
  have h2 : 2 ∈ Nat.primesLE t := Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_two⟩
  have hS : ∀ p ∈ P, p.Prime ∧ 3 ≤ p ∧ p ≤ t := by
    intro p hp
    obtain ⟨hp2, hp⟩ := mem_erase.mp hp
    obtain ⟨hpt, hprime⟩ := Nat.mem_primesLE.mp hp
    exact ⟨hprime, by have := hprime.two_le; omega, hpt⟩
  have hl := decompJ365_prime_product_lower t ht P hS
  have hprod : (∏ p ∈ P, (1 - (2 : ℝ) / p)) ≤ ∏ p ∈ P, (1 - nuN h p) := by
    apply prod_le_prod₀
    · intro p hp
      have hpR : (3 : ℝ) ≤ p := by exact_mod_cast (hS p hp).2.1
      have hi := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
        (by norm_num : (0 : ℝ) < 3) hpR
      linarith
    · intro p hp
      rw [nuN_prime (hS p hp).1]
      have hpR : (0 : ℝ) ≤ p := by positivity
      have hi := div_le_div_of_nonneg_right (wt_le_two h p) hpR
      linarith
  have hnu2 : nuN h 2 = 1 / 2 := by
    rw [nuN_prime Nat.prime_two]
    simp [LeanLab.SchnirelmannGoldbach.S1.wt, even_iff_two_dvd.mp hh]
  rw [← mul_prod_erase (Nat.primesLE t) (fun p => 1 - nuN h p) h2, hnu2]
  change _ ≤ (1 - 1 / 2 : ℝ) * ∏ p ∈ P, (1 - nuN h p)
  have hm := mul_le_mul_of_nonneg_left (hl.trans hprod) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  convert hm using 1 <;> ring

/-- Auxiliary saved level error bound for first memoir page 89.
The logarithmic factor spends only half of any supplied positive power saving. -/

lemma decomp338_level_error_upper (κ : ℝ) (hκ : 0 < κ) :
    ∀ᶠ ξ : ℕ in atTop,
      (ξ : ℝ) ^ (1 - κ) * (1 + Real.log ((ξ : ℝ) ^ (1 - κ))) ^ 2 ≤
        (1 + |1 - κ|) ^ 2 * (ξ : ℝ) ^ (1 - κ / 2) := by
  have hl : (fun x : ℝ => Real.log x ^ 2) =o[atTop] (fun x => x ^ (κ / 2)) := by
    simpa only [Real.rpow_two] using
      isLittleO_log_rpow_rpow_atTop (2 : ℝ) (show 0 < κ / 2 by positivity)
  have hg : Tendsto (fun ξ : ℕ => Real.log (ξ : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hl.natCast_atTop.def (by norm_num : (0 : ℝ) < 1),
    hg.eventually (eventually_ge_atTop (1 : ℝ)), eventually_ge_atTop 2] with ξ hlog hlarge hξ
  have hξR : (0 : ℝ) < ξ := by exact_mod_cast (by omega : 0 < ξ)
  have hlog0 : 0 ≤ Real.log ξ := by linarith
  have hlog' : Real.log ξ ^ 2 ≤ (ξ : ℝ) ^ (κ / 2) := by
    have hh : |Real.log ξ ^ 2| ≤ (ξ : ℝ) ^ (κ / 2) := by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hξR _), one_mul] using hlog
    exact (le_abs_self _).trans hh
  have hab : |1 + (1 - κ) * Real.log ξ| ≤ (1 + |1 - κ|) * Real.log ξ := by
    calc
      _ ≤ |(1 : ℝ)| + |(1 - κ) * Real.log ξ| := abs_add_le _ _
      _ = 1 + |1 - κ| * Real.log ξ := by rw [abs_mul, abs_one, abs_of_nonneg hlog0]
      _ ≤ _ := by nlinarith
  have hs : (1 + (1 - κ) * Real.log ξ) ^ 2 ≤
      (1 + |1 - κ|) ^ 2 * Real.log ξ ^ 2 := by
    have hh := mul_self_le_mul_self (abs_nonneg _) hab
    nlinarith [sq_abs (1 + (1 - κ) * Real.log ξ)]
  rw [Real.log_rpow hξR]
  calc
    _ ≤ (ξ : ℝ) ^ (1 - κ) * ((1 + |1 - κ|) ^ 2 * Real.log ξ ^ 2) :=
      mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hξR.le _)
    _ ≤ (ξ : ℝ) ^ (1 - κ) * ((1 + |1 - κ|) ^ 2 * (ξ : ℝ) ^ (κ / 2)) := by gcongr
    _ = _ := by
      rw [show (ξ : ℝ) ^ (1 - κ) * ((1 + |1 - κ|) ^ 2 * (ξ : ℝ) ^ (κ / 2)) =
        (1 + |1 - κ|) ^ 2 * ((ξ : ℝ) ^ (1 - κ) * (ξ : ℝ) ^ (κ / 2)) by ring,
        ← Real.rpow_add hξR]
      congr 2
      ring


/-- Auxiliary floor cutoff choice for the first pair on first memoir page 89.
An exponent strictly above one seventh gives both exact factor thresholds eventually. -/

lemma decomp338_floor_power_cutoff (δ : ℝ) (hδ : 1 / 7 < δ) (hδhalf : δ ≤ 1 / 2)
    (T : ℕ) :
    ∀ᶠ ξ : ℕ in atTop,
      let t := ⌊(ξ : ℝ) ^ δ⌋₊
      3 ≤ t ∧ T ≤ t ∧ t ≤ ξ ∧ (ξ : ℝ) < (t : ℝ) ^ (7 : ℕ) ∧
        (ξ : ℝ) ^ (1 / (7 : ℝ)) ≤ t := by
  have hd : 0 < δ := by linarith
  have hg := (tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop
  have hb := (tendsto_rpow_atTop (show 0 < δ - 1 / 7 by linarith)).comp
    tendsto_natCast_atTop_atTop
  filter_upwards [hg.eventually (eventually_ge_atTop ((max T 3 : ℕ) : ℝ)),
    hb.eventually (eventually_ge_atTop (4 : ℝ)), eventually_ge_atTop 2] with ξ hbig hratio hξ
  dsimp only
  let t := ⌊(ξ : ℝ) ^ δ⌋₊
  have hξ1 : (1 : ℝ) ≤ ξ := by exact_mod_cast (by omega : 1 ≤ ξ)
  have hξ0 : (0 : ℝ) < ξ := by linarith
  have htm : max T 3 ≤ t := Nat.le_floor hbig
  have hpow : (ξ : ℝ) ^ δ ≤ ξ := by
    calc _ ≤ (ξ : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hξ1 (by linarith)
         _ = _ := Real.rpow_one _
  have htξR : (t : ℝ) ≤ ξ := (Nat.floor_le (by positivity)).trans hpow
  have hr1 : (1 : ℝ) ≤ (ξ : ℝ) ^ (1 / (7 : ℝ)) := Real.one_le_rpow hξ1 (by norm_num)
  have hprod : (ξ : ℝ) ^ δ = (ξ : ℝ) ^ (δ - 1 / 7) * (ξ : ℝ) ^ (1 / (7 : ℝ)) := by
    rw [← Real.rpow_add hξ0]
    congr 1
    ring
  have hfloor := Nat.sub_one_lt_floor ((ξ : ℝ) ^ δ)
  have hroot : (ξ : ℝ) ^ (1 / (7 : ℝ)) < t := by
    have hmul : 4 * (ξ : ℝ) ^ (1 / (7 : ℝ)) ≤ (ξ : ℝ) ^ δ := by
      rw [hprod]
      exact mul_le_mul_of_nonneg_right hratio (by positivity)
    dsimp only [t]
    nlinarith
  have hroot7 : ((ξ : ℝ) ^ (1 / (7 : ℝ))) ^ (7 : ℕ) = ξ := by
    rw [← Real.rpow_mul_natCast hξ0.le]
    norm_num
  have hpower := pow_lt_pow_left₀ hroot (by positivity : (0 : ℝ) ≤ (ξ : ℝ) ^ (1 / (7 : ℝ)))
    (by norm_num : (7 : ℕ) ≠ 0)
  rw [hroot7] at hpower
  exact ⟨by omega, by omega, by exact_mod_cast htξR, hpower, hroot.le⟩

/-- The exact first Z lower leaf from its two proved supply pieces.
First memoir pages 75, 88 and 89. -/

theorem decomp338_Z_lower_6_6 :
    ∀ m : ℤ, m ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℕ, ∀ ξ : ℕ, ξ₀ ≤ ξ →
      c * ξ / Real.log ξ ^ 2 ≤ zCount 6 6 m ξ := by
  intro m hm
  obtain ⟨Y₁, hY₁, hmain⟩ := decomp338_greedy_main
  obtain ⟨Y₂, hY₂, hsupp⟩ := decomp338_greedy_support
  let Y := max Y₁ Y₂
  obtain ⟨a, ha, T, hmain⟩ := hmain Y (le_max_left _ _)
  obtain ⟨δ, κ, hδ, hδhalf, hκ, X, hsupp⟩ := hsupp Y (le_max_right _ _)
  let A : ℝ := (1 + |1 - κ|) ^ 2
  let b : ℝ := a * exp (-52 : ℝ) / 4
  have hb : 0 < b := by dsimp [b]; positivity
  apply decompJ365_lower_of_main_error hb (show 0 < κ / 2 by positivity) A
  have heven : Even (2 * m.natAbs) := ⟨m.natAbs, by omega⟩
  filter_upwards [decomp338_floor_power_cutoff δ hδ hδhalf T,
    decomp338_level_error_upper κ hκ, eventually_ge_atTop X,
    eventually_ge_atTop (max 3 (4 * m.natAbs))] with ξ hcut herr hX hξ
  let t := ⌊(ξ : ℝ) ^ δ⌋₊
  let N := ξ + 1 - 2 * m.natAbs
  let L := (ξ : ℝ) ^ (1 - κ)
  let c := decomp338GreedyCutoff (2 * m.natAbs) Y t
  let U := (Nat.primesLE t).powerset.filter (fun S =>
    ∀ j ∈ range (t + 1), (S.filter (fun p => c j < p)).card ≤ 2 * j + 1)
  let E := ∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN (2 * m.natAbs) p
  have ht3 : 3 ≤ t := hcut.1
  have hξ3 : 3 ≤ ξ := by omega
  have hξR : (1 : ℝ) < ξ := by exact_mod_cast (by omega : 1 < ξ)
  have hL : 1 ≤ L := by
    have hh := hsupp ξ (2 * m.natAbs) hX ∅ (empty_subset _) (by simp)
    simpa [L] using hh
  have hlevel : ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
      (S.filter (fun p => c j < p)).card ≤ 2 * j + 1) → ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L := by
    exact hsupp ξ (2 * m.natAbs) hX
  have hth : (ξ : ℝ) ^ (1 / ((6 : ℝ) + 1)) ≤ t := by
    convert hcut.2.2.2.2 using 1 <;> norm_num
  have hraw := decomp305_zCount_finite_lower 6 6 ξ N t m (by omega) (by dsimp [N]; omega)
    hcut.2.2.2.1 hcut.2.2.2.1 hth hth
    (range (t + 1)) c id L hL hlevel
  change (N : ℝ) * E - L * (1 + Real.log L) ^ 2 ≤ zCount 6 6 m ξ at hraw
  have hprod := decomp338_full_pair_product_lower (2 * m.natAbs) t heven ht3
  have hlogt : 0 < Real.log t := Real.log_pos (by exact_mod_cast (by omega : 1 < t))
  have hlogξ : 0 < Real.log ξ := Real.log_pos hξR
  have hlogle : Real.log t ≤ Real.log ξ := Real.log_le_log (by exact_mod_cast (by omega : 0 < t))
    (by exact_mod_cast hcut.2.2.1)
  have hprod' : exp (-52 : ℝ) / (2 * Real.log ξ ^ 2) ≤
      ∏ p ∈ Nat.primesLE t, (1 - nuN (2 * m.natAbs) p) := by
    apply le_trans _ hprod
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  have hE : a * exp (-52 : ℝ) / (2 * Real.log ξ ^ 2) ≤ E := by
    have hh := hmain (2 * m.natAbs) t heven hcut.2.1
    change a * (∏ p ∈ Nat.primesLE t, (1 - nuN (2 * m.natAbs) p)) ≤ E at hh
    calc
      _ = a * (exp (-52 : ℝ) / (2 * Real.log ξ ^ 2)) := by ring
      _ ≤ a * (∏ p ∈ Nat.primesLE t, (1 - nuN (2 * m.natAbs) p)) :=
        mul_le_mul_of_nonneg_left hprod' ha.le
      _ ≤ E := hh
  have hN : (ξ : ℝ) / 2 ≤ N := by
    have hn : ξ ≤ 2 * N := by dsimp [N]; omega
    have hnR : (ξ : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hn
    linarith
  have hmainterm : b * ξ / Real.log ξ ^ 2 ≤ (N : ℝ) * E := by
    calc
      _ = ((ξ : ℝ) / 2) * (a * exp (-52 : ℝ) / (2 * Real.log ξ ^ 2)) := by dsimp [b]; ring
      _ ≤ (N : ℝ) * (a * exp (-52 : ℝ) / (2 * Real.log ξ ^ 2)) := by gcongr
      _ ≤ (N : ℝ) * E := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _)
  change L * (1 + Real.log L) ^ 2 ≤ A * (ξ : ℝ) ^ (1 - κ / 2) at herr
  linarith

private def decomp338EncodedGap (h v t : ℕ) : ℕ := h * ∏ p ∈ (Ioc v t).filter Nat.Prime, p

/-- Auxiliary evenness of the mixed density encoding, first memoir page 88. -/

lemma decomp338_encoded_gap_even (h v t : ℕ) (heven : Even h) :
    Even (decomp338EncodedGap h v t) := by
  obtain ⟨k, hk⟩ := heven
  refine ⟨k * (∏ p ∈ (Ioc v t).filter Nat.Prime, p), ?_⟩
  unfold decomp338EncodedGap
  rw [hk]
  ring

/-- Auxiliary low prime densities for the mixed sieve on first memoir page 88.
The high prime product is coprime to every low prime, so its pair density is unchanged. -/

lemma decomp338_encoded_gap_low (h v t p : ℕ) (hp : p.Prime) (hpv : p ≤ v) :
    nuN (decomp338EncodedGap h v t) p = nuN h p := by
  have hcop : Nat.Coprime p (∏ q ∈ (Ioc v t).filter Nat.Prime, q) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    obtain ⟨hqI, hqprime⟩ := mem_filter.mp hq
    apply hp.coprime_iff_not_dvd.mpr
    intro hpd
    have heq := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp hpd
    have hqv := (mem_Ioc.mp hqI).1
    omega
  have hnot := hp.coprime_iff_not_dvd.mp hcop
  have hdiv : p ∣ decomp338EncodedGap h v t ↔ p ∣ h := by
    simp only [decomp338EncodedGap, hp.dvd_mul, hnot, or_false]
  simp only [nuN_prime hp, LeanLab.SchnirelmannGoldbach.S1.wt, hdiv]

/-- Auxiliary high prime densities for the mixed sieve on first memoir page 88.
Every encoded high prime has the one root density one over p. -/

lemma decomp338_encoded_gap_high (h v t p : ℕ) (hp : p.Prime) (hpv : v < p) (hpt : p ≤ t) :
    nuN (decomp338EncodedGap h v t) p = 1 / (p : ℝ) := by
  have hpB : p ∈ (Ioc v t).filter Nat.Prime := mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpv, hpt⟩, hp⟩
  have hprod : p ∣ ∏ q ∈ (Ioc v t).filter Nat.Prime, q := dvd_prod_of_mem id hpB
  have hd : p ∣ decomp338EncodedGap h v t := dvd_mul_of_dvd_right hprod h
  simp only [nuN_prime hp, LeanLab.SchnirelmannGoldbach.S1.wt, if_pos hd, Nat.cast_one]

/-- Auxiliary lower numerical bound for the route comparison on first memoir page 89.
The unshifted dimension two profile has tau strictly greater than two and one half. -/

lemma decomp338_tau_two_gt : (2.5 : ℝ) < ricciTau 2 := by
  have h045 : exp (0.45 : ℝ) ≤ 1.6 := ricci_exp_upper_small
    (by norm_num) (by norm_num) (by norm_num [sum_range_succ, Nat.factorial])
  have h073 : exp (0.73 : ℝ) ≤ 2.1 := ricci_exp_upper_small
    (by norm_num) (by norm_num) (by norm_num [sum_range_succ, Nat.factorial])
  have h099 : exp (0.99 : ℝ) ≤ 2.719 := by
    have hh := exp_le_exp.mpr (by norm_num : (0.99 : ℝ) ≤ 1)
    linarith [exp_one_lt_d9]
  have hn045 : (1 / 1.6 : ℝ) ≤ exp (-0.45 : ℝ) := by
    rw [exp_neg, one_div]
    exact inv_anti₀ (exp_pos _) h045
  have hn073 : (1 / 2.1 : ℝ) ≤ exp (-0.73 : ℝ) := by
    rw [exp_neg, one_div]
    exact inv_anti₀ (exp_pos _) h073
  have hn099 : (1 / 2.719 : ℝ) ≤ exp (-0.99 : ℝ) := by
    rw [exp_neg, one_div]
    exact inv_anti₀ (exp_pos _) h099
  have hq : (0.75 : ℝ) ≤ exp (-0.25 : ℝ) := by linarith [add_one_le_exp (-0.25 : ℝ)]
  have hden : 0 < 1 - exp (-0.25 : ℝ) := sub_pos.mpr (exp_lt_one_iff.mpr (by norm_num))
  have htail : (1 / 2.719 : ℝ) / 0.25 ≤ exp (-0.99 : ℝ) / (1 - exp (-0.25 : ℝ)) :=
    div_le_div₀ (by positivity) hn099 hden (by linarith)
  norm_num [ricciTau] at *
  linarith

/-- Auxiliary negative route certificate for first memoir page 89.
A cutoff exponent above one sixth cannot retain a saved power with the unshifted support profile.
This does not refute the mixed pair count. -/

lemma decomp338_prime_product_dvd_iff (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (n : ℕ) :
    (∏ p ∈ S, p) ∣ n ↔ ∀ p ∈ S, p ∣ n := by
  constructor
  · intro hd p hp
    exact (dvd_prod_of_mem id hp).trans hd
  · intro hd
    apply prod_dvd_of_isRelPrime
    · intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hS p hp) (hS q hq)).mpr hpq)
    · exact hd

/-- Auxiliary selected prime divisibility for second memoir pages 106 and 107.
Inside a finite prime set, divisibility of its selected prime product records exactly the selection predicate. -/

lemma decomp338_filtered_prime_product_dvd (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : ℕ → Prop) [DecidablePred Q] (p : ℕ) (hp : p ∈ P) :
    p ∣ (∏ q ∈ P.filter Q, q) ↔ Q p := by
  rw [(Nat.prime_iff.mp (hP p hp)).dvd_finsetProd_iff]
  constructor
  · rintro ⟨q, hq, hd⟩
    have heq := (Nat.prime_dvd_prime_iff_eq (hP p hp) (hP q (mem_filter.mp hq).1)).mp hd
    subst q
    exact (mem_filter.mp hq).2
  · intro hQ
    exact ⟨p, mem_filter.mpr ⟨hp, hQ⟩, dvd_refl p⟩

/-- Auxiliary integer encoding of the actual mixed W bad prime conditions.
Low primes divide both factor products and high primes divide the first factor.
Second memoir pages 106, 107 and 115. -/

private def decomp338MixedWProduct (N v t x : ℕ) : ℕ :=
  ∏ p ∈ (Nat.primesLE t).filter (fun p =>
    if p ≤ v then p ∣ x * (N - x) else p ∣ x), p

/-- Auxiliary exact mixed W discrepancy for second memoir pages 106, 107 and 115.
The actual low and high residue conditions have the encoded local density and root error. -/

lemma decomp338_mixed_W_remainder (N v t : ℕ) (S : Finset ℕ) (hS : S ⊆ Nat.primesLE t) :
    |(#{x ∈ range N | (∏ p ∈ S, p) ∣ decomp338MixedWProduct N v t x} : ℝ) -
      (N : ℝ) * ∏ p ∈ S, nuN (decomp338EncodedGap N v t) p| ≤
        cnt (decomp338EncodedGap N v t) (∏ p ∈ S, p) := by
  let H := decomp338EncodedGap N v t
  let A := S.filter (fun p => p ≤ v)
  let B := S.filter (fun p => v < p)
  let d := ∏ p ∈ A, p
  let e := ∏ p ∈ B, p
  have hP : ∀ p ∈ Nat.primesLE t, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => hP p (hS hp)
  have hprimeA : ∀ p ∈ A, p.Prime := fun p hp => hprime p (mem_filter.mp hp).1
  have hprimeB : ∀ p ∈ B, p.Prime := fun p hp => hprime p (mem_filter.mp hp).1
  have hAB : S = A ∪ B := by
    ext p
    simp only [A, B, mem_filter, mem_union]
    constructor
    · intro hp
      by_cases hpv : p ≤ v
      · exact Or.inl ⟨hp, hpv⟩
      · exact Or.inr ⟨hp, by omega⟩
    · intro hp
      rcases hp with hp | hp <;> exact hp.1
  have hdisj : Disjoint A B := by
    apply disjoint_left.mpr
    intro p hp hq
    have hpv := (mem_filter.mp hp).2
    have hqv := (mem_filter.mp hq).2
    omega
  have hprod : (∏ p ∈ S, p) = d * e := by rw [hAB, prod_union hdisj]
  have hd : 0 < d := prod_pos (fun p hp => (hprimeA p hp).pos)
  have he : 0 < e := prod_pos (fun p hp => (hprimeB p hp).pos)
  have hcop : Nat.Coprime d e := by
    apply Nat.Coprime.prod_left
    intro p hp
    apply Nat.Coprime.prod_right
    intro q hq
    apply (Nat.coprime_primes (hprimeA p hp) (hprimeB q hq)).mpr
    intro hpq
    have hpv := (mem_filter.mp hp).2
    have hqv := (mem_filter.mp hq).2
    omega
  have hlow (p : ℕ) (hp : p ∈ A) : wt H p = wt N p := by
    have hh := decomp338_encoded_gap_low N v t p (hprimeA p hp) (mem_filter.mp hp).2
    apply (div_left_inj' (show (p : ℝ) ≠ 0 by exact_mod_cast (hprimeA p hp).ne_zero)).mp
    simpa only [nuN_prime (hprimeA p hp)] using hh
  have hhigh (p : ℕ) (hp : p ∈ B) : wt H p = 1 := by
    have hpt := (Nat.mem_primesLE.mp (hS (mem_filter.mp hp).1)).1
    have hh := decomp338_encoded_gap_high N v t p (hprimeB p hp) (mem_filter.mp hp).2 hpt
    apply (div_left_inj' (show (p : ℝ) ≠ 0 by exact_mod_cast (hprimeB p hp).ne_zero)).mp
    simpa only [nuN_prime (hprimeB p hp)] using hh
  have hcnt : (cnt H (∏ p ∈ S, p) : ℝ) = cnt N d := by
    rw [cnt_prod_primes H S hprime, cnt_prod_primes N A hprimeA]
    calc
      _ = (∏ p ∈ A, wt H p) * ∏ p ∈ B, wt H p := by rw [hAB, prod_union hdisj]
      _ = (∏ p ∈ A, wt N p) * 1 := by
        rw [prod_congr rfl hlow, prod_eq_one hhigh]
      _ = _ := mul_one _
  have hdensity : (cnt H (∏ p ∈ S, p) : ℝ) / (∏ p ∈ S, p) = ∏ p ∈ S, nuN H p := by
    rw [cnt_prod_primes H S hprime, Nat.cast_prod, ← prod_div_distrib]
    exact prod_congr rfl (fun p hp => (nuN_prime (hprime p hp)).symm)
  have hmain : (N : ℝ) * (∏ p ∈ S, nuN H p) = (cnt N d : ℝ) * N / (d * e) := by
    rw [← hdensity, hcnt, hprod, Nat.cast_mul]
    ring
  have hcount : #{x ∈ range N | (∏ p ∈ S, p) ∣ decomp338MixedWProduct N v t x} =
      #{x ∈ range N | d ∣ x * (N - x) ∧ e ∣ x} := by
    congr 1
    apply filter_congr
    intro x hx
    have hcode (p : ℕ) (hp : p ∈ S) : p ∣ decomp338MixedWProduct N v t x ↔
        (if p ≤ v then p ∣ x * (N - x) else p ∣ x) :=
      decomp338_filtered_prime_product_dvd (Nat.primesLE t) hP _ p (hS hp)
    rw [decomp338_prime_product_dvd_iff S hprime,
      decomp338_prime_product_dvd_iff A hprimeA, decomp338_prime_product_dvd_iff B hprimeB]
    constructor
    · intro hall
      constructor
      · intro p hp
        have hh := (hcode p (mem_filter.mp hp).1).mp (hall p (mem_filter.mp hp).1)
        simpa only [if_pos (mem_filter.mp hp).2] using hh
      · intro p hp
        have hh := (hcode p (mem_filter.mp hp).1).mp (hall p (mem_filter.mp hp).1)
        simpa only [if_neg (by have := (mem_filter.mp hp).2; omega : ¬p ≤ v)] using hh
    · rintro ⟨hlo, hhi⟩ p hp
      apply (hcode p hp).mpr
      by_cases hpv : p ≤ v
      · simpa only [if_pos hpv] using hlo p (mem_filter.mpr ⟨hp, hpv⟩)
      · simpa only [if_neg hpv] using hhi p (mem_filter.mpr ⟨hp, by omega⟩)
  change |(#{x ∈ range N | (∏ p ∈ S, p) ∣ decomp338MixedWProduct N v t x} : ℝ) -
    (N : ℝ) * ∏ p ∈ S, nuN H p| ≤ cnt H (∏ p ∈ S, p)
  rw [hcount, hmain, hcnt]
  exact decompJ365_mixed_W_periodic_remainder N N d e le_rfl hd he hcop

/-- Clean supply of the finite mixed W leaf.
First memoir pages 88 and 89 and second memoir pages 106, 107 and 115.
The actual mixed residue count is kept separate from its density encoding. -/

theorem decomp338_mixed_w_finite_proved (a b N t v : ℕ) (hv : 2 ≤ v) (hvt : v ≤ t)
    (hthA : (N : ℝ) ^ (1 / ((a : ℝ) + 1)) ≤ t)
    (hthB : (N : ℝ) ^ (1 / ((b : ℝ) + 1)) ≤ v)
    (J : Finset ℕ) (cutoff level : ℕ → ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hlevel : ∀ S ⊆ Nat.primesLE t, (∀ j ∈ J,
      (S.filter (fun p : ℕ => cutoff j < p)).card ≤ 2 * level j + 1) →
        ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L) :
    let H := decomp338EncodedGap N v t
    let U := (Nat.primesLE t).powerset.filter (fun S => ∀ j ∈ J,
      (S.filter (fun p : ℕ => cutoff j < p)).card ≤ 2 * level j + 1)
    (N : ℝ) * (∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN H p) -
      L * (1 + Real.log L) ^ 2 ≤ wCount a b N := by
  let P := Nat.primesLE t
  let F := decomp338MixedWProduct N v t
  let H := decomp338EncodedGap N v t
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  have herror (S : Finset ℕ) (hS : S ⊆ P) :
      |(#{x ∈ range N | (∏ p ∈ S, p) ∣ F x} : ℝ) - (N : ℝ) * ∏ p ∈ S, nuN H p| ≤
        cnt H (∏ p ∈ S, p) := decomp338_mixed_W_remainder N v t S hS
  have hraw := decompJ365_decreasing_lower_explicit (range N) P J F hP cutoff level H N
    (nuN H) herror L hL hlevel
  apply hraw.trans
  have hincl : #{x ∈ range N | ∀ p ∈ P, ¬p ∣ F x} ≤
      #{x ∈ range N | (∀ p ∈ Nat.primesLE v, ¬p ∣ x * (N - x)) ∧
        ∀ p ∈ Nat.primesLE t \ Nat.primesLE v, ¬p ∣ x} := by
    apply card_le_card
    intro x hx
    obtain ⟨hxN, hsurv⟩ := mem_filter.mp hx
    apply mem_filter.mpr
    refine ⟨hxN, ?_, ?_⟩
    · intro p hp hd
      obtain ⟨hpv, hpprime⟩ := Nat.mem_primesLE.mp hp
      have hpP : p ∈ P := Nat.mem_primesLE.mpr ⟨hpv.trans hvt, hpprime⟩
      apply hsurv p hpP
      apply (decomp338_filtered_prime_product_dvd P hP _ p hpP).mpr
      simpa only [if_pos hpv] using hd
    · intro p hp hd
      obtain ⟨hpP, hpv⟩ := mem_sdiff.mp hp
      have hpv' : ¬p ≤ v := fun h => hpv (Nat.mem_primesLE.mpr ⟨h, hP p hpP⟩)
      apply hsurv p hpP
      apply (decomp338_filtered_prime_product_dvd P hP _ p hpP).mpr
      simpa only [if_neg hpv'] using hd
  exact_mod_cast hincl.trans (decompJ365_mixed_survivors_le_wCount a b N t v hv hvt hthA hthB)

lemma decomp338_mixed_add_periodic_remainder (h k N d e : ℕ)
    (hd : 0 < d) (he : 0 < e) (hde : Nat.Coprime d e) :
    |(#{m ∈ range N | d ∣ m * (m + h) ∧ e ∣ m + k} : ℝ) -
      (cnt h d : ℝ) * N / (d * e)| ≤ cnt h d := by
  let Q : ℕ → Prop := fun m => (-(m : ZMod d)) * ((h : ZMod d) - (-(m : ZMod d))) = 0 ∧ (m : ZMod e) + k = 0
  have hperiod : Function.Periodic Q (d * e) := by
    intro m
    simp [Q, rootPred, Nat.cast_add, Nat.cast_mul]
  have : NeZero d := ⟨hd.ne'⟩
  have : NeZero e := ⟨he.ne'⟩
  have : NeZero (d * e) := ⟨(Nat.mul_pos hd he).ne'⟩
  let E := ZMod.chineseRemainder hde
  have hcast (m : ℕ) : E (m : ZMod (d * e)) = ((m : ZMod d), (m : ZMod e)) := by
    rw [map_natCast]
    rfl
  have hcnt : #{m ∈ range (d * e) | Q m} = cnt h d := by
    rw [card_zmod_roots, Fintype.card_subtype]
    refine Finset.card_bij (fun (m : ℕ) _ => -(m : ZMod d)) ?_ ?_ ?_
    · intro m hm
      simp only [mem_filter, mem_range] at hm
      exact mem_filter.mpr ⟨mem_univ _, hm.2.1⟩
    · intro a ha b hb hab
      obtain ⟨haI, haQ⟩ := mem_filter.mp ha
      obtain ⟨hbI, hbQ⟩ := mem_filter.mp hb
      have hab' : (a : ZMod d) = (b : ZMod d) := neg_injective hab
      have heq : E (a : ZMod (d * e)) = E (b : ZMod (d * e)) := by
        rw [hcast, hcast]
        apply Prod.ext hab'
        exact add_right_cancel (haQ.2.trans hbQ.2.symm)
      have hz := congrArg ZMod.val (E.injective heq)
      simpa [ZMod.val_cast_of_lt (mem_range.mp haI),
        ZMod.val_cast_of_lt (mem_range.mp hbI)] using hz
    · intro z hz
      have hzroot := (mem_filter.mp hz).2
      let y := E.symm (-z, -(k : ZMod e))
      have hy : E (y.val : ZMod (d * e)) = (-z, -(k : ZMod e)) := by
        rw [ZMod.natCast_zmod_val]
        exact E.apply_symm_apply _
      rw [hcast] at hy
      obtain ⟨hy1, hy2⟩ := Prod.ext_iff.mp hy
      dsimp only at hy1 hy2
      refine ⟨y.val, mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt y), ?_⟩, ?_⟩
      · change (-(y.val : ZMod d)) * ((h : ZMod d) - (-(y.val : ZMod d))) = 0 ∧ (y.val : ZMod e) + k = 0
        constructor
        · simpa only [hy1, neg_neg] using hzroot
        · rw [hy2]
          simp
      · rw [hy1]
        simp
  have hdiv (m : ℕ) : d ∣ m * (m + h) ↔ (-(m : ZMod d)) * ((h : ZMod d) - (-(m : ZMod d))) = 0 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    constructor
    · intro hx
      linear_combination (-1 : ZMod d) * hx
    · intro hx
      linear_combination (-1 : ZMod d) * hx
  have hhigh (m : ℕ) : e ∣ m + k ↔ (m : ZMod e) + k = 0 := by
    simpa only [Nat.cast_add] using (ZMod.natCast_eq_zero_iff (m + k) e).symm
  have heq : #{m ∈ range N | d ∣ m * (m + h) ∧ e ∣ m + k} = #{m ∈ range N | Q m} := by
    congr 1
    apply filter_congr
    intro m hm
    change (d ∣ m * (m + h) ∧ e ∣ m + k) ↔
      ((-(m : ZMod d)) * ((h : ZMod d) - (-(m : ZMod d))) = 0 ∧ (m : ZMod e) + k = 0)
    rw [← hdiv m, ← hhigh m]
  rw [heq, ← hcnt]
  simpa only [Nat.cast_mul] using count_periodic_approx Q (Nat.mul_pos hd he) hperiod N

private def decomp338MixedZProduct (h k v t x : ℕ) : ℕ :=
  ∏ p ∈ (Nat.primesLE t).filter (fun p =>
    if p ≤ v then p ∣ x * (x + h) else p ∣ x + k), p

/-- Auxiliary actual mixed Z residue discrepancy.
The selected high factor is translated by k and the density remains the encoded pair density.
First memoir pages 75 and 88 and second memoir pages 106, 107 and 115. -/

lemma decomp338_mixed_Z_remainder (h k N v t : ℕ) (S : Finset ℕ) (hS : S ⊆ Nat.primesLE t) :
    |(#{x ∈ range N | (∏ p ∈ S, p) ∣ decomp338MixedZProduct h k v t x} : ℝ) -
      (N : ℝ) * ∏ p ∈ S, nuN (decomp338EncodedGap h v t) p| ≤
        cnt (decomp338EncodedGap h v t) (∏ p ∈ S, p) := by
  let H := decomp338EncodedGap h v t
  let A := S.filter (fun p => p ≤ v)
  let B := S.filter (fun p => v < p)
  let d := ∏ p ∈ A, p
  let e := ∏ p ∈ B, p
  have hP : ∀ p ∈ Nat.primesLE t, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => hP p (hS hp)
  have hprimeA : ∀ p ∈ A, p.Prime := fun p hp => hprime p (mem_filter.mp hp).1
  have hprimeB : ∀ p ∈ B, p.Prime := fun p hp => hprime p (mem_filter.mp hp).1
  have hAB : S = A ∪ B := by
    ext p
    simp only [A, B, mem_filter, mem_union]
    constructor
    · intro hp
      by_cases hpv : p ≤ v
      · exact Or.inl ⟨hp, hpv⟩
      · exact Or.inr ⟨hp, by omega⟩
    · intro hp
      rcases hp with hp | hp <;> exact hp.1
  have hdisj : Disjoint A B := by
    apply disjoint_left.mpr
    intro p hp hq
    have hpv := (mem_filter.mp hp).2
    have hqv := (mem_filter.mp hq).2
    omega
  have hprod : (∏ p ∈ S, p) = d * e := by rw [hAB, prod_union hdisj]
  have hd : 0 < d := prod_pos (fun p hp => (hprimeA p hp).pos)
  have he : 0 < e := prod_pos (fun p hp => (hprimeB p hp).pos)
  have hcop : Nat.Coprime d e := by
    apply Nat.Coprime.prod_left
    intro p hp
    apply Nat.Coprime.prod_right
    intro q hq
    apply (Nat.coprime_primes (hprimeA p hp) (hprimeB q hq)).mpr
    intro hpq
    have hpv := (mem_filter.mp hp).2
    have hqv := (mem_filter.mp hq).2
    omega
  have hlow (p : ℕ) (hp : p ∈ A) : wt H p = wt h p := by
    have hh := decomp338_encoded_gap_low h v t p (hprimeA p hp) (mem_filter.mp hp).2
    apply (div_left_inj' (show (p : ℝ) ≠ 0 by exact_mod_cast (hprimeA p hp).ne_zero)).mp
    simpa only [nuN_prime (hprimeA p hp)] using hh
  have hhigh (p : ℕ) (hp : p ∈ B) : wt H p = 1 := by
    have hpt := (Nat.mem_primesLE.mp (hS (mem_filter.mp hp).1)).1
    have hh := decomp338_encoded_gap_high h v t p (hprimeB p hp) (mem_filter.mp hp).2 hpt
    apply (div_left_inj' (show (p : ℝ) ≠ 0 by exact_mod_cast (hprimeB p hp).ne_zero)).mp
    simpa only [nuN_prime (hprimeB p hp)] using hh
  have hcnt : (cnt H (∏ p ∈ S, p) : ℝ) = cnt h d := by
    rw [cnt_prod_primes H S hprime, cnt_prod_primes h A hprimeA]
    calc
      _ = (∏ p ∈ A, wt H p) * ∏ p ∈ B, wt H p := by rw [hAB, prod_union hdisj]
      _ = (∏ p ∈ A, wt h p) * 1 := by
        rw [prod_congr rfl hlow, prod_eq_one hhigh]
      _ = _ := mul_one _
  have hdensity : (cnt H (∏ p ∈ S, p) : ℝ) / (∏ p ∈ S, p) = ∏ p ∈ S, nuN H p := by
    rw [cnt_prod_primes H S hprime, Nat.cast_prod, ← prod_div_distrib]
    exact prod_congr rfl (fun p hp => (nuN_prime (hprime p hp)).symm)
  have hmain : (N : ℝ) * (∏ p ∈ S, nuN H p) = (cnt h d : ℝ) * N / (d * e) := by
    rw [← hdensity, hcnt, hprod, Nat.cast_mul]
    ring
  have hcount : #{x ∈ range N | (∏ p ∈ S, p) ∣ decomp338MixedZProduct h k v t x} =
      #{x ∈ range N | d ∣ x * (x + h) ∧ e ∣ x + k} := by
    congr 1
    apply filter_congr
    intro x hx
    have hcode (p : ℕ) (hp : p ∈ S) : p ∣ decomp338MixedZProduct h k v t x ↔
        (if p ≤ v then p ∣ x * (x + h) else p ∣ x + k) :=
      decomp338_filtered_prime_product_dvd (Nat.primesLE t) hP _ p (hS hp)
    rw [decomp338_prime_product_dvd_iff S hprime,
      decomp338_prime_product_dvd_iff A hprimeA, decomp338_prime_product_dvd_iff B hprimeB]
    constructor
    · intro hall
      constructor
      · intro p hp
        have hh := (hcode p (mem_filter.mp hp).1).mp (hall p (mem_filter.mp hp).1)
        simpa only [if_pos (mem_filter.mp hp).2] using hh
      · intro p hp
        have hh := (hcode p (mem_filter.mp hp).1).mp (hall p (mem_filter.mp hp).1)
        simpa only [if_neg (by have := (mem_filter.mp hp).2; omega : ¬p ≤ v)] using hh
    · rintro ⟨hlo, hhi⟩ p hp
      apply (hcode p hp).mpr
      by_cases hpv : p ≤ v
      · simpa only [if_pos hpv] using hlo p (mem_filter.mpr ⟨hp, hpv⟩)
      · simpa only [if_neg hpv] using hhi p (mem_filter.mpr ⟨hp, by omega⟩)
  change |(#{x ∈ range N | (∏ p ∈ S, p) ∣ decomp338MixedZProduct h k v t x} : ℝ) -
    (N : ℝ) * ∏ p ∈ S, nuN H p| ≤ cnt H (∏ p ∈ S, p)
  rw [hcount, hmain, hcnt]
  exact decomp338_mixed_add_periodic_remainder h k N d e hd he hcop

lemma decomp338_mixed_survivors_le_zCount (a b ξ N t v : ℕ) (m : ℤ)
    (hv : 2 ≤ v) (hvt : v ≤ t) (hN : N + 2 * m.natAbs ≤ ξ + 1)
    (hsizeA : (ξ : ℝ) < (t : ℝ) ^ (a + 1))
    (hsizeB : (ξ : ℝ) < (v : ℝ) ^ (b + 1))
    (hthA : (ξ : ℝ) ^ (1 / ((a : ℝ) + 1)) ≤ t)
    (hthB : (ξ : ℝ) ^ (1 / ((b : ℝ) + 1)) ≤ v) :
    #{y ∈ range N | (∀ p ∈ Nat.primesLE v, ¬ p ∣ y * (y + 2 * m.natAbs)) ∧
      ∀ p ∈ Nat.primesLE t \ Nat.primesLE v, ¬p ∣ y + (if 0 ≤ m then 0 else 2 * m.natAbs)} ≤
      zCount a b m ξ := by
  have ht : 2 ≤ t := hv.trans hvt
  let h := 2 * m.natAbs
  let f : ℕ → ℕ := fun y => if 0 ≤ m then y else y + h
  have hgap : (h : ℤ) = 2 * |m| := by simp [h, Int.natCast_natAbs]
  have hvalues (y : ℕ) :
      (f y : ℤ) + 2 * m = if 0 ≤ m then (y + h : ℕ) else y := by
    dsimp [f]
    split_ifs with hm
    · rw [abs_of_nonneg hm] at hgap
      push_cast
      omega
    · rw [abs_of_neg (lt_of_not_ge hm)] at hgap
      push_cast
      omega
  apply Finset.card_le_card_of_injOn f
  · intro y hy
    obtain ⟨hyN, hlo, hhi⟩ := mem_filter.mp hy
    have hylt := mem_range.mp hyN
    have hy0 : 0 < y := by
      by_contra hy
      have hz : y = 0 := by omega
      have htwo : 2 ∈ Nat.primesLE v := Nat.mem_primesLE.mpr ⟨hv, Nat.prime_two⟩
      exact hlo 2 htwo (by simp [hz])
    have hyξ : y + h ≤ ξ := by dsimp [h]; omega
    have hx1 : 1 ≤ f y := by dsimp [f]; split_ifs <;> omega
    have hxξ : f y ≤ ξ := by dsimp [f]; split_ifs <;> omega
    have hbpos : 0 < (f y : ℤ) + 2 * m := by
      rw [hvalues]
      split_ifs <;> positivity
    have hrough (z : ℕ) (hz : z = y ∨ z = y + h) :
        ∀ p ∈ z.primeFactorsList, (v : ℝ) < p := by
      intro p hp
      have hz0 : z ≠ 0 := by rcases hz with rfl | rfl <;> omega
      obtain ⟨hpprime, hpdvd⟩ := (Nat.mem_primeFactorsList hz0).mp hp
      by_contra htp
      have hpt : p ≤ v := by exact_mod_cast (le_of_not_gt htp : (p : ℝ) ≤ v)
      have hpP := Nat.mem_primesLE.mpr ⟨hpt, hpprime⟩
      apply hlo p hpP
      rcases hz with rfl | rfl
      · exact dvd_mul_of_dvd_left hpdvd _
      · exact dvd_mul_of_dvd_right hpdvd _
    have hfy : f y = y ∨ f y = y + h := by dsimp [f]; split_ifs <;> simp
    have hroughA : ∀ p ∈ (f y).primeFactorsList, (t : ℝ) < p := by
      intro p hp
      obtain ⟨hpprime, hpdvd⟩ := (Nat.mem_primeFactorsList (by omega : f y ≠ 0)).mp hp
      by_contra htp
      have hpt : p ≤ t := by exact_mod_cast (le_of_not_gt htp : (p : ℝ) ≤ t)
      have hpP := Nat.mem_primesLE.mpr ⟨hpt, hpprime⟩
      by_cases hpv : p ≤ v
      · apply hlo p (Nat.mem_primesLE.mpr ⟨hpv, hpprime⟩)
        rcases hfy with hf | hf
        · rw [hf] at hpdvd
          exact dvd_mul_of_dvd_left hpdvd _
        · rw [hf] at hpdvd
          exact dvd_mul_of_dvd_right hpdvd _
      · apply hhi p (mem_sdiff.mpr ⟨hpP, fun hp => hpv (Nat.mem_primesLE.mp hp).1⟩)
        dsimp [f, h] at hpdvd
        split_ifs at hpdvd ⊢ <;> simpa using hpdvd
    have hbval : ((f y : ℤ) + 2 * m).toNat = if 0 ≤ m then y + h else y := by
      rw [hvalues]
      split_ifs <;> norm_cast
    have hb1 : 1 ≤ ((f y : ℤ) + 2 * m).toNat := by rw [hbval]; split_ifs <;> omega
    have hbξ : ((f y : ℤ) + 2 * m).toNat ≤ ξ := by rw [hbval]; split_ifs <;> omega
    have hbchoices : ((f y : ℤ) + 2 * m).toNat = y ∨
        ((f y : ℤ) + 2 * m).toNat = y + h := by rw [hbval]; split_ifs <;> simp
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (by omega : 1 ≤ t)
    have hv1 : (1 : ℝ) ≤ v := by exact_mod_cast (by omega : 1 ≤ v)
    have hA := almostGT_of_pow_bound hx1 ht1 hroughA
      ((by exact_mod_cast hxξ : (f y : ℝ) ≤ ξ).trans_lt hsizeA)
    have hB := almostGT_of_pow_bound hb1 hv1 (hrough _ hbchoices)
      ((by exact_mod_cast hbξ : (((f y : ℤ) + 2 * m).toNat : ℝ) ≤ ξ).trans_lt hsizeB)
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨hx1, hxξ⟩, almostGT_mono hA le_rfl ?_, hbpos,
      almostGT_mono hB le_rfl ?_⟩
    · exact (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hxξ)
        (by positivity)).trans hthA
    · exact (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hxξ)
        (by positivity)).trans hthB
  · intro y _ z _ heq
    dsimp [f] at heq
    split_ifs at heq <;> omega

theorem decomp338_mixed_z_finite_proved (a b ξ N t v : ℕ) (m : ℤ) (hv : 2 ≤ v) (hvt : v ≤ t)
    (hN : N + 2 * m.natAbs ≤ ξ + 1)
    (hsizeA : (ξ : ℝ) < (t : ℝ) ^ (a + 1)) (hsizeB : (ξ : ℝ) < (v : ℝ) ^ (b + 1))
    (hthA : (ξ : ℝ) ^ (1 / ((a : ℝ) + 1)) ≤ t)
    (hthB : (ξ : ℝ) ^ (1 / ((b : ℝ) + 1)) ≤ v)
    (J : Finset ℕ) (cutoff level : ℕ → ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hlevel : ∀ S ⊆ Nat.primesLE t, (∀ j ∈ J,
      (S.filter (fun p : ℕ => cutoff j < p)).card ≤ 2 * level j + 1) →
        ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L) :
    let H := decomp338EncodedGap (2 * m.natAbs) v t
    let U := (Nat.primesLE t).powerset.filter (fun S => ∀ j ∈ J,
      (S.filter (fun p : ℕ => cutoff j < p)).card ≤ 2 * level j + 1)
    (N : ℝ) * (∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN H p) -
      L * (1 + Real.log L) ^ 2 ≤ zCount a b m ξ := by

  let P := Nat.primesLE t
  let h := 2 * m.natAbs
  let k := if 0 ≤ m then 0 else h
  let F := decomp338MixedZProduct h k v t
  let H := decomp338EncodedGap h v t
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  have herror (S : Finset ℕ) (hS : S ⊆ P) :
      |(#{x ∈ range N | (∏ p ∈ S, p) ∣ F x} : ℝ) - (N : ℝ) * ∏ p ∈ S, nuN H p| ≤
        cnt H (∏ p ∈ S, p) := decomp338_mixed_Z_remainder h k N v t S hS
  have hraw := decompJ365_decreasing_lower_explicit (range N) P J F hP cutoff level H N
    (nuN H) herror L hL hlevel
  apply hraw.trans
  have hincl : #{x ∈ range N | ∀ p ∈ P, ¬p ∣ F x} ≤
      #{x ∈ range N | (∀ p ∈ Nat.primesLE v, ¬p ∣ x * (x + h)) ∧
        ∀ p ∈ Nat.primesLE t \ Nat.primesLE v, ¬p ∣ x + k} := by
    apply card_le_card
    intro x hx
    obtain ⟨hxN, hsurv⟩ := mem_filter.mp hx
    apply mem_filter.mpr
    refine ⟨hxN, ?_, ?_⟩
    · intro p hp hd
      obtain ⟨hpv, hpprime⟩ := Nat.mem_primesLE.mp hp
      have hpP : p ∈ P := Nat.mem_primesLE.mpr ⟨hpv.trans hvt, hpprime⟩
      apply hsurv p hpP
      apply (decomp338_filtered_prime_product_dvd P hP _ p hpP).mpr
      simpa only [if_pos hpv] using hd
    · intro p hp hd
      obtain ⟨hpP, hpv⟩ := mem_sdiff.mp hp
      have hpv' : ¬p ≤ v := fun h => hpv (Nat.mem_primesLE.mpr ⟨h, hP p hpP⟩)
      apply hsurv p hpP
      apply (decomp338_filtered_prime_product_dvd P hP _ p hpP).mpr
      simpa only [if_neg hpv'] using hd
  exact_mod_cast hincl.trans (decomp338_mixed_survivors_le_zCount a b ξ N t v m hv hvt hN hsizeA hsizeB hthA hthB)

lemma decomp338_mixed_low_block (h y w v t : ℕ) (hwv : w ≤ v) :
    (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN (decomp338EncodedGap h v t) p) =
      ∑ p ∈ (Ioc y w).filter Nat.Prime, nuN h p := by
  apply sum_congr rfl
  intro p hp
  obtain ⟨hpI, hpprime⟩ := mem_filter.mp hp
  exact decomp338_encoded_gap_low h v t p hpprime ((mem_Ioc.mp hpI).2.trans hwv)

/-- Auxiliary high block identity for the mixed density on first memoir page 88.
Every density in the high part is one over its prime. -/

lemma decomp338_mixed_high_block (h y w v t : ℕ) (hvy : v ≤ y) (hwt : w ≤ t) :
    (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN (decomp338EncodedGap h v t) p) =
      ∑ p ∈ (Ioc y w).filter Nat.Prime, (1 : ℝ) / p := by
  apply sum_congr rfl
  intro p hp
  obtain ⟨hpI, hpprime⟩ := mem_filter.mp hp
  obtain ⟨hyp, hpw⟩ := mem_Ioc.mp hpI
  exact decomp338_encoded_gap_high h v t p hpprime (hvy.trans_lt hyp) (hpw.trans hwt)

/-- Auxiliary exact mixed mass split for first memoir page 88 and second memoir page 115.
The low contribution has the original pair density and the high contribution has one root. -/

lemma decomp338_mixed_mass_split (h y v w t : ℕ) (hyv : y ≤ v) (hvw : v ≤ w) (hwt : w ≤ t) :
    (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN (decomp338EncodedGap h v t) p) =
      (∑ p ∈ (Ioc y v).filter Nat.Prime, nuN h p) +
        ∑ p ∈ (Ioc v w).filter Nat.Prime, (1 : ℝ) / p := by
  have hs := sum_Ioc_consecutive
    (fun p => if p.Prime then nuN (decomp338EncodedGap h v t) p else 0) hyv hvw
  rw [← sum_filter, ← sum_filter, ← sum_filter] at hs
  rw [← hs, decomp338_mixed_low_block h y v v t le_rfl,
    decomp338_mixed_high_block h v w v t le_rfl hwt]

/-- Auxiliary mixed mass upper bound for first memoir page 88 and second memoir page 115.
Below the transition v the logarithmic coefficient is two and above it the coefficient is one. -/

lemma decomp338_mixed_mass_upper (h y v w t : ℕ) (hy : 2 ≤ y)
    (hyv : y ≤ v) (hvw : v ≤ w) (hwt : w ≤ t) :
    (∑ p ∈ (Ioc y w).filter Nat.Prime, nuN (decomp338EncodedGap h v t) p) ≤
      2 * Real.log (Real.log v / Real.log y) + Real.log (Real.log w / Real.log v) +
        28 / Real.log y + 14 / Real.log v := by
  rw [decomp338_mixed_mass_split h y v w t hyv hvw hwt]
  have hlo := decompJ365_pair_block_mass_upper h y v hy hyv
  have hhi := decompJ365_prime_block_upper v w (hy.trans hyv) hvw
  linarith

/-- Auxiliary endpoint location for the mixed sieve on second memoir page 115.
If the entire high prime mass fits the first printed target, the first greedy cutoff is at most v. -/

lemma decomp338_mixed_first_cutoff_le (h Y v t : ℕ) (hYv : Y ≤ v) (hvt : v ≤ t)
    (hmass : (∑ p ∈ (Ioc v t).filter Nat.Prime, (1 : ℝ) / p) ≤ 0.90) :
    decomp338GreedyCutoff (decomp338EncodedGap h v t) Y t 0 ≤ v := by
  have hex : ∃ y : ℕ, Y ≤ y ∧ y ≤ t ∧
      (∑ p ∈ (Ioc y t).filter Nat.Prime, nuN (decomp338EncodedGap h v t) p) ≤
        (decomp305HeadMass 0 : ℝ) / 100 := by
    refine ⟨v, hYv, hvt, ?_⟩
    rw [decomp338_mixed_high_block h v t v t le_rfl le_rfl]
    norm_num [decomp305HeadMass] at *
    exact hmass
  change decomp338GreedyStep (decomp338EncodedGap h v t) Y t 0 ≤ v
  unfold decomp338GreedyStep
  rw [dif_pos hex]
  apply Nat.find_min' hex
  refine ⟨hYv, hvt, ?_⟩
  rw [decomp338_mixed_high_block h v t v t le_rfl le_rfl]
  norm_num [decomp305HeadMass] at *
  exact hmass

lemma decomp338_mixed_block_cutoff_upper (h y v w t : ℕ) (θ ε ω : ℝ)
    (hy : 2 ≤ y) (hyv : y ≤ v) (hvw : v ≤ w) (hwt : w ≤ t)
    (hmass : θ - ε ≤ ∑ p ∈ (Ioc y w).filter Nat.Prime, nuN (decomp338EncodedGap h v t) p)
    (hend : 28 / Real.log y + 14 / Real.log v ≤ ε)
    (hshift : ω ≤ Real.log (Real.log w / Real.log v)) :
    (y : ℝ) ≤ (w : ℝ) ^ Real.exp (-(θ + ω) / 2 + ε) := by
  have hyw : y ≤ w := hyv.trans hvw
  have hyR : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hwR : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have hly : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hlw : 0 < Real.log w := Real.log_pos (by exact_mod_cast (by omega : 1 < w))
  have hmain := decomp338_mixed_mass_upper h y v w t hy hyv hvw hwt
  have hlv : 0 < Real.log v := Real.log_pos (by exact_mod_cast (by omega : 1 < v))
  have hlogs :
      2 * Real.log (Real.log v / Real.log y) + Real.log (Real.log w / Real.log v) =
        2 * Real.log (Real.log w / Real.log y) - Real.log (Real.log w / Real.log v) := by
    simp only [Real.log_div hlv.ne' hly.ne', Real.log_div hlw.ne' hlv.ne',
      Real.log_div hlw.ne' hly.ne']
    ring
  rw [hlogs] at hmain
  have hl : (θ + ω) / 2 - ε ≤ Real.log (Real.log w / Real.log y) := by linarith
  have hexp : Real.exp ((θ + ω) / 2 - ε) ≤ Real.log w / Real.log y := by
    simpa only [Real.exp_log (div_pos hlw hly)] using Real.exp_le_exp.mpr hl
  have hm := (le_div_iff₀ hly).mp hexp
  have hm' := mul_le_mul_of_nonneg_left hm (Real.exp_pos (-(θ + ω) / 2 + ε)).le
  have he : Real.exp (-(θ + ω) / 2 + ε) * Real.exp ((θ + ω) / 2 - ε) = 1 := by
    rw [← Real.exp_add]
    rw [show (-(θ + ω) / 2 + ε) + ((θ + ω) / 2 - ε) = 0 by ring, Real.exp_zero]
  rw [← mul_assoc, he, one_mul] at hm'
  apply (Real.log_le_log_iff hyR (Real.rpow_pos_of_pos hwR _)).mp
  rwa [Real.log_rpow hwR]

/-- Auxiliary actual shifted first endpoint bound for first memoir page 89 cases two and three.
Second memoir page 115, the unnumbered display referring to formulas 31.3 and 31.4.
The shift is retained in the first exponent rather than discarded by a dimension two bound. -/

lemma decomp338_mixed_first_power_max (h Y v t : ℕ) (hY : 4 ≤ Y)
    (hYv : Y ≤ v) (hvt : v ≤ t) (ε ω : ℝ)
    (hhigh : (∑ p ∈ (Ioc v t).filter Nat.Prime, (1 : ℝ) / p) ≤ 0.90)
    (hsmall : ∀ y : ℕ, Y ≤ y → 2 / (y : ℝ) ≤ ε ∧ 42 / Real.log y ≤ ε)
    (hshift : ω ≤ Real.log (Real.log t / Real.log v)) :
    (decomp338GreedyCutoff (decomp338EncodedGap h v t) Y t 0 : ℝ) ≤
      max (Y : ℝ) ((t : ℝ) ^ exp (-(0.90 + ω) / 2 + ε)) := by
  let H := decomp338EncodedGap h v t
  let y := decomp338GreedyStep H Y t 0
  obtain ⟨hyY, hyt, hmass⟩ := decomp338_greedy_step_bounds H Y t 0 (hYv.trans hvt)
  have hyv : y ≤ v := decomp338_mixed_first_cutoff_le h Y v t hYv hvt hhigh
  change (y : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ exp (-(0.90 + ω) / 2 + ε))
  by_cases heq : y = Y
  · rw [heq]
    exact le_max_left _ _
  · have hyY' : Y < y := by omega
    have hm := decomp338_greedy_step_mass_lower H Y t 0 (hYv.trans hvt) hyY'
    have herr := hsmall y hyY
    have hlo : 0.90 - ε ≤ ∑ p ∈ (Ioc y t).filter Nat.Prime, nuN H p := by
      norm_num [decomp305HeadMass] at hm
      linarith
    have hly : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
    have hlog : Real.log y ≤ Real.log v :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < y)) (by exact_mod_cast hyv)
    have hdiv : 14 / Real.log v ≤ 14 / Real.log y :=
      div_le_div_of_nonneg_left (by norm_num) hly hlog
    have hend : 28 / Real.log y + 14 / Real.log v ≤ ε := by
      have he : 28 / Real.log y + 14 / Real.log y = 42 / Real.log y := by ring
      linarith
    have hp := decomp338_mixed_block_cutoff_upper h y v t t 0.90 ε ω
      (by omega) hyv hvt le_rfl hlo hend hshift
    exact hp.trans (le_max_right _ _)

lemma decomp338_nested_floor_cutoff (δ r γ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1) (hγ : 0 < γ) (hgap : γ < δ * r) (K : ℕ) :
    ∀ᶠ ξ : ℕ in atTop,
      let t := ⌊(ξ : ℝ) ^ δ⌋₊
      let v := ⌊(t : ℝ) ^ r⌋₊
      K ≤ v ∧ v ≤ t ∧ t ≤ ξ ∧ (ξ : ℝ) ^ γ < v := by
  have hc : Tendsto (fun ξ : ℕ => (ξ : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ht := (tendsto_rpow_atTop hδ).comp hc
  have hg := (tendsto_rpow_atTop hγ).comp hc
  have hd := (tendsto_rpow_atTop (show 0 < δ * r - γ by linarith)).comp hc
  filter_upwards [ht.eventually (eventually_ge_atTop (4 : ℝ)),
    hg.eventually (eventually_ge_atTop (K : ℝ)),
    hd.eventually (eventually_ge_atTop (8 : ℝ)), eventually_ge_atTop 2] with ξ ht4 hK hratio hξ
  dsimp only
  let t := ⌊(ξ : ℝ) ^ δ⌋₊
  let v := ⌊(t : ℝ) ^ r⌋₊
  have hξ0 : (0 : ℝ) < ξ := by exact_mod_cast (by omega : 0 < ξ)
  have hξ1 : (1 : ℝ) ≤ ξ := by exact_mod_cast (by omega : 1 ≤ ξ)
  have ht4N : 4 ≤ t := Nat.le_floor ht4
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (by omega : 1 ≤ t)
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have htlower : (ξ : ℝ) ^ δ / 2 ≤ (t : ℝ) := by
    have hh := Nat.sub_one_lt_floor ((ξ : ℝ) ^ δ)
    change (ξ : ℝ) ^ δ - 1 < (t : ℝ) at hh
    linarith
  have htwo : (2 : ℝ) ^ r ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hr1
  have hrpow := Real.rpow_le_rpow (show 0 ≤ (ξ : ℝ) ^ δ / 2 by positivity) htlower hr.le
  rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hξ0.le] at hrpow
  have hhalf : (ξ : ℝ) ^ (δ * r) / 2 ≤ (t : ℝ) ^ r := by
    apply le_trans _ hrpow
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) htwo
  have hroot1 : (1 : ℝ) ≤ (ξ : ℝ) ^ γ := Real.one_le_rpow hξ1 hγ.le
  have hprod : (ξ : ℝ) ^ (δ * r) = (ξ : ℝ) ^ (δ * r - γ) * (ξ : ℝ) ^ γ := by
    rw [← Real.rpow_add hξ0]
    congr 1
    ring
  have hmul : 8 * (ξ : ℝ) ^ γ ≤ (ξ : ℝ) ^ (δ * r) := by
    rw [hprod]
    exact mul_le_mul_of_nonneg_right hratio (by positivity)
  have hvfloor := Nat.sub_one_lt_floor ((t : ℝ) ^ r)
  change (t : ℝ) ^ r - 1 < (v : ℝ) at hvfloor
  have hroot : (ξ : ℝ) ^ γ < (v : ℝ) := by nlinarith
  have hvtR : (v : ℝ) ≤ t := by
    calc
      _ ≤ (t : ℝ) ^ r := Nat.floor_le (by positivity)
      _ ≤ (t : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 hr1
      _ = _ := Real.rpow_one _
  have htξR : (t : ℝ) ≤ ξ := by
    calc
      _ ≤ (ξ : ℝ) ^ δ := Nat.floor_le (by positivity)
      _ ≤ (ξ : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hξ1 hδ1
      _ = _ := Real.rpow_one _
  exact ⟨by exact_mod_cast hK.trans hroot.le, by exact_mod_cast hvtR,
    by exact_mod_cast htξR, hroot⟩

/-- Auxiliary factor count size margin for first memoir page 89.
A strict prime threshold bound gives the exact next integer power bound. -/

lemma decomp338_size_of_root_lt (a ξ t : ℕ)
    (hr : (ξ : ℝ) ^ (1 / ((a : ℝ) + 1)) < t) :
    (ξ : ℝ) < (t : ℝ) ^ (a + 1) := by
  have hh := (Real.rpow_inv_lt_iff_of_pos (Nat.cast_nonneg ξ) (Nat.cast_nonneg t)
    (show 0 < (a : ℝ) + 1 by positivity)).mp (by simpa only [one_div] using hr)
  rw [show (a : ℝ) + 1 = ((a + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast] at hh
  exact hh

lemma decomp338_log_twenty_ninths : Real.log (20 / 9 : ℝ) ≤ 0.8 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 20 / 9)).mpr
  exact ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial])

/-- Auxiliary eventual high mass and exact logarithmic shift for a floored mixed cutoff.
First memoir page 89 cases two and three and second memoir page 115 after 31.3 and 31.4.
Ratios above 0.45 put the entire high mass strictly below the first target 0.90. -/

lemma decomp338_mixed_high_mass_eventually (r : ℝ) (hr : 0.45 < r) (hr1 : r ≤ 1) :
    ∀ᶠ t : ℕ in atTop,
      let v := ⌊(t : ℝ) ^ r⌋₊
      2 ≤ v ∧ v ≤ t ∧
        (∑ p ∈ (Ioc v t).filter Nat.Prime, (1 : ℝ) / p) ≤ 0.85 ∧
        -Real.log r ≤ Real.log (Real.log t / Real.log v) := by
  have hloggrowth : Tendsto (fun v : ℕ => Real.log (v : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (hloggrowth.eventually (eventually_ge_atTop (280 : ℝ)))
  have hfloor := decomp338_nested_floor_cutoff 1 r 0.45 (by norm_num) le_rfl
    (by linarith) hr1 (by norm_num) (by simpa using hr) (max K 2)
  filter_upwards [hfloor, eventually_ge_atTop 2] with t ht ht2
  simp only [Real.rpow_one, Nat.floor_natCast] at ht
  dsimp only
  let v := ⌊(t : ℝ) ^ r⌋₊
  obtain ⟨hKv, hvt, _, hroot⟩ := ht
  have hv2 : 2 ≤ v := by omega
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hlv : 0 < Real.log v := Real.log_pos (by exact_mod_cast (by omega : 1 < v))
  have hlt : 0 < Real.log t := Real.log_pos (by exact_mod_cast (by omega : 1 < t))
  have hlow : 0.45 * Real.log t ≤ Real.log v := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos ht0 _) hroot.le
    rwa [Real.log_rpow ht0] at hh
  have hquot : Real.log t / Real.log v ≤ (20 / 9 : ℝ) := by
    apply (div_le_iff₀ hlv).mpr
    linarith
  have hratio := Real.log_le_log (div_pos hlt hlv) hquot
  have herr : 14 / Real.log v ≤ (0.05 : ℝ) := by
    apply (div_le_iff₀ hlv).mpr
    have hh := hK v (by omega)
    linarith
  have hmass := decompJ365_prime_block_upper v t hv2 hvt
  have hmass' : (∑ p ∈ (Ioc v t).filter Nat.Prime, (1 : ℝ) / p) ≤ 0.85 := by
    linarith [decomp338_log_twenty_ninths]
  have hvfloor : (v : ℝ) ≤ (t : ℝ) ^ r := Nat.floor_le (by positivity)
  have hlogupper := Real.log_le_log (by exact_mod_cast (by omega : 0 < v)) hvfloor
  rw [Real.log_rpow ht0] at hlogupper
  have hr0 : 0 < r := by linarith
  have hquotlow : 1 / r ≤ Real.log t / Real.log v := by
    apply (le_div_iff₀ hlv).mpr
    have hh : Real.log v / r ≤ Real.log t := (div_le_iff₀ hr0).mpr (by nlinarith)
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hh
  have hshift := Real.log_le_log (by positivity : (0 : ℝ) < 1 / r) hquotlow
  rw [Real.log_div one_ne_zero hr0.ne', Real.log_one, zero_sub] at hshift
  exact ⟨hv2, hvt, hmass', hshift⟩

/-- Auxiliary eventual first endpoint location for the first two mixed pairs.
First memoir page 89 cases two and three, second memoir page 115 after 31.3 and 31.4. -/

lemma decomp338_greedy_two_mass_lower (h Y t : ℕ) (hY : 4 ≤ Y) (hYt : Y ≤ t)
    (hstop : Y < decomp338GreedyCutoff h Y t 1) :
    1.46 - 4 / (decomp338GreedyCutoff h Y t 1 : ℝ) <
      ∑ p ∈ (Ioc (decomp338GreedyCutoff h Y t 1) t).filter Nat.Prime, nuN h p := by
  let c := decomp338GreedyCutoff h Y t
  obtain ⟨hc, hlo, htop⟩ := decomp338_greedy_cutoff_bounds h Y t hYt
  change Y < c 1 at hstop
  change ∀ i, Y ≤ c i at hlo
  change c 0 ≤ t at htop
  have h10 : c 1 ≤ c 0 := hc (by omega)
  have hfirst := decomp338_greedy_step_mass_lower h Y t 0 hYt (by change Y < c 0; omega)
  have hsecond := decomp338_greedy_step_mass_lower h Y (c 0) 1 (hlo 0) hstop
  have hsplit := sum_Ioc_consecutive (fun p => if p.Prime then nuN h p else 0) h10 htop
  rw [← sum_filter, ← sum_filter, ← sum_filter] at hsplit
  have hpos : (0 : ℝ) < c 1 := by exact_mod_cast (by have := hlo 1; omega : 0 < c 1)
  have hdiv : 2 / (c 0 : ℝ) ≤ 2 / (c 1 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hpos (by exact_mod_cast h10)
  norm_num only [decomp305HeadMass, Nat.cast_ofNat] at hfirst hsecond
  change (9 / 10 : ℝ) - 2 / (c 0 : ℝ) <
    ∑ p ∈ (Ioc (c 0) t).filter Nat.Prime, nuN h p at hfirst
  change (14 / 25 : ℝ) - 2 / (c 1 : ℝ) <
    ∑ p ∈ (Ioc (c 1) (c 0)).filter Nat.Prime, nuN h p at hsecond
  change 1.46 - 4 / (c 1 : ℝ) <
    ∑ p ∈ (Ioc (c 1) t).filter Nat.Prime, nuN h p
  have he : 4 / (c 1 : ℝ) = 2 / (c 1 : ℝ) + 2 / (c 1 : ℝ) := by ring
  rw [he]
  linarith

/-- Auxiliary second endpoint location for first memoir page 89 case four.
A high mass at most 1.40 cannot contain the first two target masses 1.46 above a residual cutoff one hundred.
Second memoir page 115 after formulas 31.3 and 31.4. -/

lemma decomp338_mixed_second_cutoff_le (h Y v t : ℕ) (hY : 100 ≤ Y)
    (hYv : Y ≤ v) (hvt : v ≤ t)
    (hhigh : (∑ p ∈ (Ioc v t).filter Nat.Prime, (1 : ℝ) / p) ≤ 1.40) :
    decomp338GreedyCutoff (decomp338EncodedGap h v t) Y t 1 ≤ v := by
  let H := decomp338EncodedGap h v t
  let y := decomp338GreedyCutoff H Y t 1
  change y ≤ v
  by_contra hnot
  have hvy : v < y := by omega
  have hyY : Y < y := hYv.trans_lt hvy
  have hlow := decomp338_greedy_two_mass_lower H Y t (by omega) (hYv.trans hvt) hyY
  have hupper : (∑ p ∈ (Ioc y t).filter Nat.Prime, nuN H p) ≤ 1.40 := by
    rw [decomp338_mixed_high_block h y t v t hvy.le le_rfl]
    apply le_trans _ hhigh
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpI, hpprime⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hvy.trans (mem_Ioc.mp hpI).1, (mem_Ioc.mp hpI).2⟩, hpprime⟩
    · intro p hp _
      positivity
  have hy100 : (100 : ℝ) ≤ y := by exact_mod_cast (by omega : 100 ≤ y)
  have hdiv : 4 / (y : ℝ) ≤ 0.04 := by
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < y)).mpr
    linarith
  change 1.46 - 4 / (y : ℝ) < _ at hlow
  linarith

/-- Auxiliary actual shifted second endpoint power for first memoir page 89 case four.
Second memoir page 115 after formulas 31.3 and 31.4.
The cumulative lower mass is 1.46 and the logarithmic shift is retained. -/

lemma decomp338_mixed_second_power_max (h Y v t : ℕ) (hY : 100 ≤ Y)
    (hYv : Y ≤ v) (hvt : v ≤ t) (ε ω : ℝ)
    (hhigh : (∑ p ∈ (Ioc v t).filter Nat.Prime, (1 : ℝ) / p) ≤ 1.40)
    (hsmall : ∀ y : ℕ, Y ≤ y → 4 / (y : ℝ) ≤ ε ∧ 42 / Real.log y ≤ ε)
    (hshift : ω ≤ Real.log (Real.log t / Real.log v)) :
    (decomp338GreedyCutoff (decomp338EncodedGap h v t) Y t 1 : ℝ) ≤
      max (Y : ℝ) ((t : ℝ) ^ exp (-(1.46 + ω) / 2 + ε)) := by
  let H := decomp338EncodedGap h v t
  let y := decomp338GreedyCutoff H Y t 1
  have hyY := (decomp338_greedy_cutoff_bounds H Y t (hYv.trans hvt)).2.1 1
  have hyv : y ≤ v := decomp338_mixed_second_cutoff_le h Y v t hY hYv hvt hhigh
  change (y : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ exp (-(1.46 + ω) / 2 + ε))
  by_cases heq : y = Y
  · rw [heq]
    exact le_max_left _ _
  · have hyY' : Y < y := by omega
    have hm := decomp338_greedy_two_mass_lower H Y t (by omega) (hYv.trans hvt) hyY'
    obtain ⟨herr1, herr2⟩ := hsmall y hyY
    have hlo : 1.46 - ε ≤ ∑ p ∈ (Ioc y t).filter Nat.Prime, nuN H p := by linarith
    have hly : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
    have hlog : Real.log y ≤ Real.log v :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < y)) (by exact_mod_cast hyv)
    have hdiv : 14 / Real.log v ≤ 14 / Real.log y :=
      div_le_div_of_nonneg_left (by norm_num) hly hlog
    have hend : 28 / Real.log y + 14 / Real.log v ≤ ε := by
      have he : 28 / Real.log y + 14 / Real.log y = 42 / Real.log y := by ring
      linarith
    exact (decomp338_mixed_block_cutoff_upper h y v t t 1.46 ε ω
      (by omega) hyv hvt le_rfl hlo hend hshift).trans (le_max_right _ _)

lemma decomp338_log_thousand_249 : Real.log (1000 / 249 : ℝ) ≤ 1.395 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 1000 / 249)).mpr
  exact ricci_exp_lower (by norm_num) (by norm_num [sum_range_succ, Nat.factorial])

/-- Auxiliary eventual high mass and exact logarithmic shift for a floored mixed cutoff.
First memoir page 89 case four and second memoir page 115 after 31.3 and 31.4.
Ratios above 0.249 put the entire high mass strictly below the first two targets totaling 1.46. -/

lemma decomp338_case_four_high_mass_eventually (r : ℝ) (hr : 0.249 < r) (hr1 : r ≤ 1) :
    ∀ᶠ t : ℕ in atTop,
      let v := ⌊(t : ℝ) ^ r⌋₊
      2 ≤ v ∧ v ≤ t ∧
        (∑ p ∈ (Ioc v t).filter Nat.Prime, (1 : ℝ) / p) ≤ 1.40 ∧
        -Real.log r ≤ Real.log (Real.log t / Real.log v) := by
  have hloggrowth : Tendsto (fun v : ℕ => Real.log (v : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (hloggrowth.eventually (eventually_ge_atTop (2800 : ℝ)))
  have hfloor := decomp338_nested_floor_cutoff 1 r 0.249 (by norm_num) le_rfl
    (by linarith) hr1 (by norm_num) (by simpa using hr) (max K 2)
  filter_upwards [hfloor, eventually_ge_atTop 2] with t ht ht2
  simp only [Real.rpow_one, Nat.floor_natCast] at ht
  dsimp only
  let v := ⌊(t : ℝ) ^ r⌋₊
  obtain ⟨hKv, hvt, _, hroot⟩ := ht
  have hv2 : 2 ≤ v := by omega
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hlv : 0 < Real.log v := Real.log_pos (by exact_mod_cast (by omega : 1 < v))
  have hlt : 0 < Real.log t := Real.log_pos (by exact_mod_cast (by omega : 1 < t))
  have hlow : 0.249 * Real.log t ≤ Real.log v := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos ht0 _) hroot.le
    rwa [Real.log_rpow ht0] at hh
  have hquot : Real.log t / Real.log v ≤ (1000 / 249 : ℝ) := by
    apply (div_le_iff₀ hlv).mpr
    linarith
  have hratio := Real.log_le_log (div_pos hlt hlv) hquot
  have herr : 14 / Real.log v ≤ (0.005 : ℝ) := by
    apply (div_le_iff₀ hlv).mpr
    have hh := hK v (by omega)
    linarith
  have hmass := decompJ365_prime_block_upper v t hv2 hvt
  have hmass' : (∑ p ∈ (Ioc v t).filter Nat.Prime, (1 : ℝ) / p) ≤ 1.40 := by
    linarith [decomp338_log_thousand_249]
  have hvfloor : (v : ℝ) ≤ (t : ℝ) ^ r := Nat.floor_le (by positivity)
  have hlogupper := Real.log_le_log (by exact_mod_cast (by omega : 0 < v)) hvfloor
  rw [Real.log_rpow ht0] at hlogupper
  have hr0 : 0 < r := by linarith
  have hquotlow : 1 / r ≤ Real.log t / Real.log v := by
    apply (le_div_iff₀ hlv).mpr
    have hh : Real.log v / r ≤ Real.log t := (div_le_iff₀ hr0).mpr (by nlinarith)
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hh
  have hshift := Real.log_le_log (by positivity : (0 : ℝ) < 1 / r) hquotlow
  rw [Real.log_div one_ne_zero hr0.ne', Real.log_one, zero_sub] at hshift
  exact ⟨hv2, hvt, hmass', hshift⟩

lemma decomp338_profile_from_first (h Y t : ℕ) (hY : 4 ≤ Y) (hYt : Y ≤ t)
    (ε : ℝ) (α : ℕ → ℝ)
    (hsmall : ∀ y : ℕ, Y ≤ y → 2 / (y : ℝ) ≤ ε ∧ 28 / Real.log y ≤ ε)
    (hfirst : (decomp338GreedyCutoff h Y t 0 : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α 1)))
    (hrec : ∀ i, α (i + 2) = α (i + 1) * exp (-(decomp305HeadMass (i + 1) : ℝ) / 100 / 2 + ε))
    (i : ℕ) :
    (decomp338GreedyCutoff h Y t i : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α (i + 1))) := by
  let c := decomp338GreedyCutoff h Y t
  have hlo := (decomp338_greedy_cutoff_bounds h Y t hYt).2.1
  induction i with
  | zero => exact hfirst
  | succ i ih =>
    change (c (i + 1) : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α (i + 2)))
    change (c i : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α (i + 1))) at ih
    by_cases hp : (t : ℝ) ^ (α (i + 1)) ≤ Y
    · have hci : (c i : ℝ) ≤ Y := by simpa only [max_eq_left hp] using ih
      have hs : (c (i + 1) : ℝ) ≤ c i := by
        exact_mod_cast decomp338_greedy_step_le h Y (c i) (i + 1)
      exact hs.trans (hci.trans (le_max_left _ _))
    · have hci : (c i : ℝ) ≤ (t : ℝ) ^ (α (i + 1)) := by
        simpa only [max_eq_right (le_of_lt (lt_of_not_ge hp))] using ih
      let r := exp (-(decomp305HeadMass (i + 1) : ℝ) / 100 / 2 + ε)
      have hstep := decomp338_greedy_step_power_max h Y (c i) (i + 1) hY (hlo i) ε hsmall
      change (c (i + 1) : ℝ) ≤ max (Y : ℝ) ((c i : ℝ) ^ r) at hstep
      have hrpow : (c i : ℝ) ^ r ≤ ((t : ℝ) ^ (α (i + 1))) ^ r :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hci (exp_pos _).le
      have heq : ((t : ℝ) ^ (α (i + 1))) ^ r = (t : ℝ) ^ (α (i + 2)) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg _), hrec i]
      have hle : (c i : ℝ) ^ r ≤ (t : ℝ) ^ (α (i + 2)) := hrpow.trans_eq heq
      exact hstep.trans (max_le_max_left _ hle)

/-- Auxiliary shifted geometric profile for first memoir page 89 cases two and three.
Second memoir pages 113 to 115, formulas 31.3 to 31.5 and their mixed variant.
Scaling every positive depth by exp of half log r preserves the later recurrence. -/

lemma decomp338_shifted_support_profile (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ ε : ℝ, ∃ α : ℕ → ℝ, 0 < ε ∧ ε < 1 / 4 ∧ α 0 = 1 ∧
      (∀ i, 0 < α i) ∧ (∀ i, α (i + 1) ≤ α i) ∧
      (∀ n, (∑ i ∈ range n, α (i + 1)) ≤ exp (Real.log r / 2) * ricciTau 2 + 0.001) ∧
      α 1 = exp (-(0.90 - Real.log r) / 2 + ε) ∧
      ∀ i, α (i + 2) = α (i + 1) * exp (-(decomp305HeadMass (i + 1) : ℝ) / 100 / 2 + ε) := by
  obtain ⟨ε, a, hε0, hε, ha0, hapos, hamono, hasum, ha1, ha2, hatail⟩ :=
    decompJ365_support_profile 0.001 (by norm_num)
  obtain ⟨_, harec⟩ := decomp338_support_profile_recurrence ε a ha1 ha2 hatail
  let s := exp (Real.log r / 2)
  have hs0 : 0 < s := exp_pos _
  have hs1 : s ≤ 1 := exp_le_one_iff.mpr (by linarith [Real.log_nonpos hr.le hr1])
  let α : ℕ → ℝ := fun i => if i = 0 then 1 else s * a i
  have hαpos (i : ℕ) : 0 < α i := by
    dsimp [α]
    split_ifs
    · norm_num
    · exact mul_pos hs0 (hapos i)
  have hαmono (i : ℕ) : α (i + 1) ≤ α i := by
    rcases i with _ | i
    · change s * a 1 ≤ 1
      have ha := hamono 0
      rw [ha0] at ha
      nlinarith [hapos 1]
    · simpa only [α, ite_eq_right (by omega : i + 1 + 1 ≠ 0),
        ite_eq_right (by omega : i + 1 ≠ 0)] using
        mul_le_mul_of_nonneg_left (hamono (i + 1)) hs0.le
  refine ⟨ε, α, hε0, hε, by simp [α], hαpos, hαmono, ?_, ?_, ?_⟩
  · intro n
    have hsum : (∑ i ∈ range n, α (i + 1)) = s * ∑ i ∈ range n, a (i + 1) := by
      simp only [α, Nat.add_one_ne_zero, ite_false, mul_sum]
    rw [hsum]
    have hh := mul_le_mul_of_nonneg_left (hasum n) hs0.le
    dsimp [s] at *
    nlinarith
  · change s * a 1 = _
    rw [ha1, ← exp_add]
    congr 1
    ring
  · intro i
    change s * a (i + 2) = (s * a (i + 1)) * _
    rw [harec i]
    ring

lemma decomp338_mixed_support_from_parameters (a b : ℕ) (r δ κ : ℝ)
    (hr : 0.45 < r) (hr1 : r ≤ 1) (hδ0 : 0 < δ)
    (hδA : 1 / ((a : ℝ) + 1) < δ) (hδhalf : δ ≤ 1 / 2)
    (hδB : 1 / ((b : ℝ) + 1) < δ * r) (hκ : 0 < κ)
    (hsave : δ * (1 + 2 * (exp (Real.log r / 2) * ricciTau 2 + 0.001)) ≤ 1 - κ) :
    ∃ Y₀ : ℕ, 4 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ δ κ : ℝ, 1 / ((a : ℝ) + 1) < δ ∧ δ ≤ 1 / 2 ∧
        1 / ((b : ℝ) + 1) < δ * r ∧ 0 < κ ∧
        ∃ X : ℕ, ∀ ξ h : ℕ, X ≤ ξ →
          let t := ⌊(ξ : ℝ) ^ δ⌋₊
          let v := ⌊(t : ℝ) ^ r⌋₊
          let H := decomp338EncodedGap h v t
          ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
            (S.filter (fun p : ℕ => decomp338GreedyCutoff H Y t j < p)).card ≤ 2 * j + 1) →
              ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (ξ : ℝ) ^ (1 - κ) := by
  obtain ⟨ε, α, hε0, hε, hα0, hαpos, hαmono, hαsum, hα1, hrec⟩ :=
    decomp338_shifted_support_profile r (by linarith) hr1
  obtain ⟨Y₀, hY₀, hsmall₀⟩ := decomp338_endpoint_error_threshold (ε * (2 / 3)) (by positivity)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (decomp338_mixed_high_mass_eventually r hr hr1)
  refine ⟨Y₀, hY₀, ?_⟩
  intro Y hY
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp
    (decomp338_nested_floor_cutoff 1 r 0.45 (by norm_num) le_rfl
      (by linarith) hr1 (by norm_num) (by simpa using hr) Y)
  let T := max T₁ T₂
  refine ⟨δ, κ / 2, hδA, hδhalf, hδB, by positivity, ?_⟩
  let C : ℕ := ∏ p ∈ Nat.primesLE Y, p
  have hCpos : 0 < C := by
    apply prod_pos
    intro p hp
    exact (Nat.mem_primesLE.mp hp).2.pos
  have hcast : Tendsto (fun ξ : ℕ => (ξ : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hδ0).comp hcast).eventually
      (eventually_ge_atTop ((max (max Y 2) T : ℕ) : ℝ)))
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (show 0 < κ / 2 by positivity)).comp hcast).eventually
      (eventually_ge_atTop (C : ℝ)))
  refine ⟨max 2 (max X₁ X₂), ?_⟩
  intro ξ h hξ
  dsimp only
  let t := ⌊(ξ : ℝ) ^ δ⌋₊
  let v := ⌊(t : ℝ) ^ r⌋₊
  let H := decomp338EncodedGap h v t
  intro S hS hcaps
  change S ⊆ Nat.primesLE t at hS
  change ∀ j ∈ range (t + 1),
    (S.filter (fun p : ℕ => decomp338GreedyCutoff H Y t j < p)).card ≤ 2 * j + 1 at hcaps
  have hξ2 : 2 ≤ ξ := by omega
  have hξ0 : (0 : ℝ) < ξ := by exact_mod_cast (by omega : 0 < ξ)
  have hξ1 : (1 : ℝ) ≤ ξ := by exact_mod_cast (by omega : 1 ≤ ξ)
  have htm : max (max Y 2) T ≤ t := Nat.le_floor (hX₁ ξ (by omega))
  have hYt : Y ≤ t := by omega
  have hY4 : 4 ≤ Y := hY₀.trans hY
  have ht2 : 2 ≤ t := by omega
  have hsmall42 : ∀ y : ℕ, Y ≤ y → 2 / (y : ℝ) ≤ ε ∧ 42 / Real.log y ≤ ε := by
    intro y hy
    obtain ⟨h1, h2⟩ := hsmall₀ y (hY.trans hy)
    have he : 42 / Real.log y = (3 / 2 : ℝ) * (28 / Real.log y) := by ring
    constructor <;> nlinarith
  have hsmall : ∀ y : ℕ, Y ≤ y → 2 / (y : ℝ) ≤ ε ∧ 28 / Real.log y ≤ ε := by
    intro y hy
    obtain ⟨h1, h2⟩ := hsmall₀ y (hY.trans hy)
    constructor <;> linarith
  have hhigh := hT₁ t (by dsimp [T] at htm; omega)
  have hvlarge := hT₂ t (by dsimp [T] at htm; omega)
  simp only [Real.rpow_one, Nat.floor_natCast] at hvlarge
  have hYv : Y ≤ v := hvlarge.1
  have hvt : v ≤ t := hhigh.2.1
  have hfirst : (decomp338GreedyCutoff H Y t 0 : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α 1)) := by
    rw [hα1]
    have hp := decomp338_mixed_first_power_max h Y v t hY4 hYv hvt ε (-Real.log r)
      (by linarith [hhigh.2.2.1]) hsmall42 hhigh.2.2.2
    simpa only [sub_eq_add_neg] using hp
  have hprofile := decomp338_profile_from_first H Y t hY4 hYt ε α hsmall hfirst hrec
  have hstop := decomp338_greedy_stops H Y t hY4 hYt
  let A := S.filter (fun p => Y < p)
  let B := S.filter (fun p => p ≤ Y)
  have hAB : S = A ∪ B := by
    ext p
    simp only [A, B, mem_filter, mem_union]
    constructor
    · intro hp
      by_cases hy : Y < p
      · exact Or.inl ⟨hp, hy⟩
      · exact Or.inr ⟨hp, by omega⟩
    · intro hp
      rcases hp with hp | hp <;> exact hp.1
  have hdisj : Disjoint A B := by
    apply disjoint_left.mpr
    intro p hp hq
    have hpY := (mem_filter.mp hp).2
    have hqY := (mem_filter.mp hq).2
    omega
  have hBsub : B ⊆ Nat.primesLE Y := by
    intro p hp
    obtain ⟨hpS, hpY⟩ := mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpY, (Nat.mem_primesLE.mp (hS hpS)).2⟩
  have hBbound : (∏ p ∈ B, p) ≤ C :=
    Nat.le_of_dvd hCpos (prod_dvd_prod_of_subset B (Nat.primesLE Y) id hBsub)
  have hcard : A.card ≤ 2 * t + 1 := by
    have hh := hcaps t (mem_range.mpr (by omega : t < t + 1))
    simpa only [hstop] using hh
  have hAcaps : ∀ i ∈ range t,
      (A.filter (fun p : ℕ => (t : ℝ) ^ (α (i + 1)) < (p : ℝ))).card ≤ 2 * i + 1 := by
    intro i hi
    have hsub : A.filter (fun p : ℕ => (t : ℝ) ^ (α (i + 1)) < (p : ℝ)) ⊆
        S.filter (fun p : ℕ => decomp338GreedyCutoff H Y t i < p) := by
      intro p hp
      obtain ⟨hpA, hpow⟩ := mem_filter.mp hp
      obtain ⟨hpS, hpY⟩ := mem_filter.mp hpA
      have hpYR : (Y : ℝ) < p := by exact_mod_cast hpY
      have hmax : max (Y : ℝ) ((t : ℝ) ^ (α (i + 1))) < p := max_lt_iff.mpr ⟨hpYR, hpow⟩
      have hcR := (hprofile i).trans_lt hmax
      exact mem_filter.mpr ⟨hpS, by exact_mod_cast hcR⟩
    exact (card_le_card hsub).trans (hcaps i (mem_range.mpr (by have := mem_range.mp hi; omega)))
  have htop : (t : ℝ) ≤ (ξ : ℝ) ^ δ := Nat.floor_le (by positivity)
  have hApos : ∀ p ∈ A, 0 < p := by
    intro p hp
    exact (Nat.mem_primesLE.mp (hS (mem_filter.mp hp).1)).2.pos
  have hAmax : ∀ p ∈ A, (p : ℝ) ≤ t := by
    intro p hp
    exact_mod_cast (Nat.mem_primesLE.mp (hS (mem_filter.mp hp).1)).1
  have hτ : 0 ≤ exp (Real.log r / 2) * ricciTau 2 + 0.001 := by
    simpa using hαsum 0
  have hlarge := decompJ365_nested_saved_support A ξ t δ
    (exp (Real.log r / 2) * ricciTau 2 + 0.001) κ hξ1
    (by exact_mod_cast (by omega : 1 < t)) htop hτ hκ α hαmono hα0 t
    (hαpos t).le (hαsum t) hApos hAmax hcard hAcaps hsave
  have hsmallprod : ((∏ p ∈ B, p : ℕ) : ℝ) ≤ C := by exact_mod_cast hBbound
  have hCbound : (C : ℝ) ≤ (ξ : ℝ) ^ (κ / 2) := hX₂ ξ (by omega)
  have hsplit : ((∏ p ∈ S, p : ℕ) : ℝ) =
      ((∏ p ∈ A, p : ℕ) : ℝ) * ((∏ p ∈ B, p : ℕ) : ℝ) := by
    rw [hAB, prod_union hdisj, Nat.cast_mul]
  calc
    _ = ((∏ p ∈ A, p : ℕ) : ℝ) * ((∏ p ∈ B, p : ℕ) : ℝ) := hsplit
    _ ≤ (ξ : ℝ) ^ (1 - κ) * (C : ℝ) :=
      mul_le_mul hlarge hsmallprod (Nat.cast_nonneg _) (Real.rpow_nonneg hξ0.le _)
    _ ≤ (ξ : ℝ) ^ (1 - κ) * (ξ : ℝ) ^ (κ / 2) :=
      mul_le_mul_of_nonneg_left hCbound (Real.rpow_nonneg hξ0.le _)
    _ = (ξ : ℝ) ^ (1 - κ / 2) := by
      rw [← Real.rpow_add hξ0]
      congr 1
      ring

theorem decomp338_mixed_support_5_7_proved :
    ∃ Y₀ : ℕ, 4 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ δ κ : ℝ, 1 / ((5 : ℝ) + 1) < δ ∧ δ ≤ 1 / 2 ∧
        1 / ((7 : ℝ) + 1) < δ * (3 / 4 : ℝ) ∧ 0 < κ ∧
        ∃ X : ℕ, ∀ ξ h : ℕ, X ≤ ξ →
          let t := ⌊(ξ : ℝ) ^ δ⌋₊
          let v := ⌊(t : ℝ) ^ (3 / 4 : ℝ)⌋₊
          let H := decomp338EncodedGap h v t
          ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
            (S.filter (fun p : ℕ => decomp338GreedyCutoff H Y t j < p)).card ≤ 2 * j + 1) →
              ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (ξ : ℝ) ^ (1 - κ) := by
  have hm := decompJ365_first_four_saved_exponents
  dsimp only at hm
  obtain ⟨δ, κ, hδ0, hκ, hδA, hδB, hsave⟩ := hm.2.1
  norm_num at hδA hδB
  have hδ : 1 / ((5 : ℝ) + 1) < min δ (1 / 2) := lt_min (by norm_num; exact hδA) (by norm_num)
  have hδr : 1 / ((7 : ℝ) + 1) < min δ (1 / 2) * (3 / 4 : ℝ) := by
    have hh : (4 / 3 : ℝ) / (7 + 1) < min δ (1 / 2) := lt_min (by norm_num; exact hδB) (by norm_num)
    norm_num at hh ⊢
    linarith
  have hlog : Real.log (3 / 4 : ℝ) = -Real.log (4 / 3 : ℝ) := by
    rw [show (3 / 4 : ℝ) = (4 / 3 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hτ : 0 ≤ ricciTau 2 := by linarith [decomp338_tau_two_gt]
  have hC : 0 ≤ 1 + 2 * (exp (Real.log (3 / 4 : ℝ) / 2) * ricciTau 2 + 0.001) := by positivity
  apply decomp338_mixed_support_from_parameters 5 7 (3 / 4) (min δ (1 / 2)) κ
    (by norm_num) (by norm_num) (by linarith) hδ (min_le_right _ _) hδr hκ
  apply (mul_le_mul_of_nonneg_right (min_le_left δ (1 / 2)) hC).trans
  rw [hlog]
  convert hsave using 1 <;> ring

/-- Clean supplier of the shifted support for first memoir page 89 case three.
Second memoir pages 113 to 115, formulas 31.3 to 31.5 and their mixed variant. -/

theorem decomp338_mixed_support_4_9_proved :
    ∃ Y₀ : ℕ, 4 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ δ κ : ℝ, 1 / ((4 : ℝ) + 1) < δ ∧ δ ≤ 1 / 2 ∧
        1 / ((9 : ℝ) + 1) < δ * (1 / 2 : ℝ) ∧ 0 < κ ∧
        ∃ X : ℕ, ∀ ξ h : ℕ, X ≤ ξ →
          let t := ⌊(ξ : ℝ) ^ δ⌋₊
          let v := ⌊(t : ℝ) ^ (1 / 2 : ℝ)⌋₊
          let H := decomp338EncodedGap h v t
          ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
            (S.filter (fun p : ℕ => decomp338GreedyCutoff H Y t j < p)).card ≤ 2 * j + 1) →
              ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (ξ : ℝ) ^ (1 - κ) := by
  have hm := decompJ365_first_four_saved_exponents
  dsimp only at hm
  obtain ⟨δ, κ, hδ0, hκ, hδA, hδB, hsave⟩ := hm.2.2.1
  norm_num at hδA hδB
  have hδ : 1 / ((4 : ℝ) + 1) < min δ (1 / 2) := lt_min (by norm_num; exact hδA) (by norm_num)
  have hδr : 1 / ((9 : ℝ) + 1) < min δ (1 / 2) * (1 / 2 : ℝ) := by
    have hh : (2 : ℝ) / (9 + 1) < min δ (1 / 2) := lt_min (by norm_num; exact hδB) (by norm_num)
    norm_num at hh ⊢
    linarith
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log (2 : ℝ) := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hτ : 0 ≤ ricciTau 2 := by linarith [decomp338_tau_two_gt]
  have hC : 0 ≤ 1 + 2 * (exp (Real.log (1 / 2 : ℝ) / 2) * ricciTau 2 + 0.001) := by positivity
  apply decomp338_mixed_support_from_parameters 4 9 (1 / 2) (min δ (1 / 2)) κ
    (by norm_num) (by norm_num) (by linarith) hδ (min_le_right _ _) hδr hκ
  apply (mul_le_mul_of_nonneg_right (min_le_left δ (1 / 2)) hC).trans
  rw [hlog]
  convert hsave using 1 <;> ring

lemma decomp338_one_dimensional_cutoff_upper (y w : ℕ) (θ ε : ℝ)
    (hy : 2 ≤ y) (hyw : y ≤ w)
    (hmass : θ - ε ≤ ∑ p ∈ (Ioc y w).filter Nat.Prime, (1 : ℝ) / p)
    (hend : 14 / Real.log y ≤ ε) :
    (y : ℝ) ≤ (w : ℝ) ^ Real.exp (-θ + 2 * ε) := by
  have hyR : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hwR : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have hly : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hlw : 0 < Real.log w := Real.log_pos (by exact_mod_cast (by omega : 1 < w))
  have hmain := decompJ365_prime_block_upper y w hy hyw
  have hl : θ - 2 * ε ≤ Real.log (Real.log w / Real.log y) := by linarith
  have hexp : Real.exp (θ - 2 * ε) ≤ Real.log w / Real.log y := by
    simpa only [Real.exp_log (div_pos hlw hly)] using Real.exp_le_exp.mpr hl
  have hm := (le_div_iff₀ hly).mp hexp
  have hm' := mul_le_mul_of_nonneg_left hm (Real.exp_pos (-θ + 2 * ε)).le
  have he : Real.exp (-θ + 2 * ε) * Real.exp (θ - 2 * ε) = 1 := by
    rw [← Real.exp_add]
    rw [show (-θ + 2 * ε) + (θ - 2 * ε) = 0 by ring, Real.exp_zero]
  rw [← mul_assoc, he, one_mul] at hm'
  apply (Real.log_le_log_iff hyR (Real.rpow_pos_of_pos hwR _)).mp
  rwa [Real.log_rpow hwR]


/-- Auxiliary actual first endpoint power for first memoir page 89 case four.
Below v the trivial v bound suffices. Above v the block has dimension one.
Second memoir page 115, mixed variant after 31.3 and 31.4. -/

lemma decomp338_case_four_first_power (h Y v t : ℕ) (hY : 4 ≤ Y)
    (hYv : Y ≤ v) (hvt : v ≤ t) (hvpow : (v : ℝ) ≤ (t : ℝ) ^ (1 / 4 : ℝ))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : ∀ y : ℕ, Y ≤ y → 2 / (y : ℝ) ≤ ε ∧ 14 / Real.log y ≤ ε) :
    (decomp338GreedyCutoff (decomp338EncodedGap h v t) Y t 0 : ℝ) ≤
      max (Y : ℝ) ((t : ℝ) ^ exp (-0.90 + 2 * ε)) := by
  let H := decomp338EncodedGap h v t
  let y := decomp338GreedyCutoff H Y t 0
  obtain ⟨hyY, hyt, _⟩ := decomp338_greedy_step_bounds H Y t 0 (hYv.trans hvt)
  change (y : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ exp (-0.90 + 2 * ε))
  by_cases hyv : y ≤ v
  · have hexp : (1 / 4 : ℝ) ≤ exp (-0.90 + 2 * ε) := by
      have h4 : exp (0.90 : ℝ) ≤ 4 := (exp_le_exp.mpr (by norm_num : (0.90 : ℝ) ≤ 1)).trans
        (by linarith [exp_one_lt_d9])
      have hh : (1 / 4 : ℝ) ≤ exp (-0.90 : ℝ) := by
        rw [exp_neg]
        simpa using inv_anti₀ (exp_pos (0.90 : ℝ)) h4
      exact hh.trans (exp_le_exp.mpr (by linarith))
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (by omega : 1 ≤ t)
    exact (le_trans (by exact_mod_cast hyv) (hvpow.trans
      (Real.rpow_le_rpow_of_exponent_le ht1 hexp))).trans (le_max_right _ _)
  · have hvy : v < y := by omega
    have hm := decomp338_greedy_step_mass_lower H Y t 0 (hYv.trans hvt) (hYv.trans_lt hvy)
    change (decomp305HeadMass 0 : ℝ) / 100 - 2 / (y : ℝ) <
      ∑ p ∈ (Ioc y t).filter Nat.Prime, nuN H p at hm
    rw [decomp338_mixed_high_block h y t v t hvy.le le_rfl] at hm
    have herr := hsmall y hyY
    have hlo : 0.90 - ε ≤ ∑ p ∈ (Ioc y t).filter Nat.Prime, (1 : ℝ) / p := by
      have heq : (decomp305HeadMass 0 : ℝ) / 100 = 0.90 := by norm_num [decomp305HeadMass]
      rw [heq] at hm
      linarith
    exact (decomp338_one_dimensional_cutoff_upper y t 0.90 ε (by omega) hyt hlo herr.2).trans
      (le_max_right _ _)

lemma decomp338_case_four_perturbation (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 4 ∧
      exp (-0.90 + 2 * ε) + exp (-(1.46 + Real.log 4) / 2 + 2 * ε) +
        exp (-(1.98 + Real.log 4) / 2 + 3 * ε) / (1 - exp (-0.50 / 2 + ε)) < (exp (-0.90 : ℝ) + exp (-(Real.log (4 : ℝ)) / 2) * (exp (-1.46 / 2) + exp (-1.98 / 2) / (1 - exp (-0.50 / 2)))) + η := by
  let g : ℝ → ℝ := fun ε => exp (-0.90 + 2 * ε) + exp (-(1.46 + Real.log 4) / 2 + 2 * ε) +
    exp (-(1.98 + Real.log 4) / 2 + 3 * ε) / (1 - exp (-0.50 / 2 + ε))
  have hd : 1 - exp (-0.50 / 2 : ℝ) ≠ 0 := by
    have he : exp (-0.50 / 2 : ℝ) < 1 := exp_lt_one_iff.mpr (by norm_num)
    linarith
  have hg0 : g 0 = (exp (-0.90 : ℝ) + exp (-(Real.log (4 : ℝ)) / 2) * (exp (-1.46 / 2) + exp (-1.98 / 2) / (1 - exp (-0.50 / 2)))) := by
    dsimp [g]
    simp only [mul_zero, add_zero]
    have h2 : exp (-(1.46 + Real.log (4 : ℝ)) / 2) = exp (-Real.log 4 / 2) * exp (-1.46 / 2) := by
      rw [← exp_add]
      congr 1
      ring
    have h3 : exp (-(1.98 + Real.log (4 : ℝ)) / 2) = exp (-Real.log 4 / 2) * exp (-1.98 / 2) := by
      rw [← exp_add]
      congr 1
      ring
    rw [h2, h3]
    ring
  have hcont : ContinuousAt g 0 := by
    dsimp [g]
    fun_prop (disch := simpa using hd)
  have hnear : ∀ᶠ ε : ℝ in nhds 0, g ε < (exp (-0.90 : ℝ) + exp (-(Real.log (4 : ℝ)) / 2) * (exp (-1.46 / 2) + exp (-1.98 / 2) / (1 - exp (-0.50 / 2)))) + η :=
    hcont.tendsto.eventually (eventually_lt_nhds (by rw [hg0]; linarith))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let ε := min (δ / 2) (1 / 8)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨ε, hε, lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  apply hball
  simpa [Real.dist_eq, abs_of_pos hε] using hεδ

/-- Auxiliary case four profile estimate for first memoir page 89, the tau bar display.
Second memoir pages 113 to 115, formulas 31.3 to 31.5 and their mixed variant. -/

lemma decomp338_case_four_geometric_sum (ε : ℝ) (hε : ε < 1 / 4) (n : ℕ) :
    let a : ℕ → ℝ := fun i => if i = 0 then exp (-0.90 + 2 * ε)
      else if i = 1 then exp (-(1.46 + Real.log 4) / 2 + 2 * ε)
      else exp (-(1.98 + Real.log 4) / 2 + 3 * ε) * exp (-0.50 / 2 + ε) ^ (i - 2)
    (∑ i ∈ range n, a i) ≤
      exp (-0.90 + 2 * ε) + exp (-(1.46 + Real.log 4) / 2 + 2 * ε) +
        exp (-(1.98 + Real.log 4) / 2 + 3 * ε) / (1 - exp (-0.50 / 2 + ε)) := by
  dsimp only
  let q := exp (-0.50 / 2 + ε)
  have hq0 : 0 ≤ q := (exp_pos _).le
  have hq1 : q < 1 := exp_lt_one_iff.mpr (by linarith)
  have hgeom (k : ℕ) : (∑ i ∈ range k, q ^ i) ≤ 1 / (1 - q) := by
    have hsum := (hasSum_geometric_of_lt_one hq0 hq1).summable.sum_le_tsum
      (range k) (fun i _ => pow_nonneg hq0 i)
    simpa only [(hasSum_geometric_of_lt_one hq0 hq1).tsum_eq, one_div] using hsum
  rcases n with _ | n
  · simp only [range_zero, sum_empty]
    positivity
  rcases n with _ | n
  · simp only [Nat.zero_add, range_one, sum_singleton]
    have hd : 0 < 1 - q := sub_pos.mpr hq1
    change exp (-0.90 + 2 * ε) ≤ exp (-0.90 + 2 * ε) +
      exp (-(1.46 + Real.log 4) / 2 + 2 * ε) + exp (-(1.98 + Real.log 4) / 2 + 3 * ε) / (1 - q)
    have hcdiv : 0 ≤ exp (-(1.98 + Real.log 4) / 2 + 3 * ε) / (1 - q) :=
      div_nonneg (exp_pos _).le hd.le
    linarith [exp_pos (-(1.46 + Real.log 4) / 2 + 2 * ε)]
  · rw [show n + 1 + 1 = 2 + n by omega, sum_range_add]
    have hhead : (∑ i ∈ range 2, if i = 0 then exp (-0.90 + 2 * ε)
        else if i = 1 then exp (-(1.46 + Real.log 4) / 2 + 2 * ε)
        else exp (-(1.98 + Real.log 4) / 2 + 3 * ε) * exp (-0.50 / 2 + ε) ^ (i - 2)) =
          exp (-0.90 + 2 * ε) + exp (-(1.46 + Real.log 4) / 2 + 2 * ε) := by
      norm_num [sum_range_succ]
    rw [hhead]
    have htail : (∑ i ∈ range n,
        if 2 + i = 0 then exp (-0.90 + 2 * ε)
        else if 2 + i = 1 then exp (-(1.46 + Real.log 4) / 2 + 2 * ε)
        else exp (-(1.98 + Real.log 4) / 2 + 3 * ε) * q ^ (2 + i - 2)) =
          exp (-(1.98 + Real.log 4) / 2 + 3 * ε) * ∑ i ∈ range n, q ^ i := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      have h1 : 2 + i ≠ 1 := by omega
      simp [h1, show 2 + i - 2 = i by omega]
    change _ ≤ exp (-0.90 + 2 * ε) + exp (-(1.46 + Real.log 4) / 2 + 2 * ε) +
      exp (-(1.98 + Real.log 4) / 2 + 3 * ε) / (1 - q)
    rw [htail]
    have hh := mul_le_mul_of_nonneg_left (hgeom n) (exp_pos (-(1.98 + Real.log 4) / 2 + 3 * ε)).le
    simpa only [mul_one_div, add_comm] using add_le_add_left hh
      (exp (-0.90 + 2 * ε) + exp (-(1.46 + Real.log 4) / 2 + 2 * ε))

/-- Auxiliary case four profile estimate for first memoir page 89, the tau bar display.
Second memoir pages 113 to 115, formulas 31.3 to 31.5 and their mixed variant. -/

lemma decomp338_case_four_support_profile (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, ∃ α : ℕ → ℝ, 0 < ε ∧ ε < 1 / 4 ∧ α 0 = 1 ∧
      (∀ i, 0 < α i) ∧ (∀ i, α (i + 1) ≤ α i) ∧
      (∀ n, (∑ i ∈ range n, α (i + 1)) ≤ (exp (-0.90 : ℝ) + exp (-(Real.log (4 : ℝ)) / 2) * (exp (-1.46 / 2) + exp (-1.98 / 2) / (1 - exp (-0.50 / 2)))) + η) ∧
      α 1 = exp (-0.90 + 2 * ε) ∧ α 2 = exp (-(1.46 + Real.log 4) / 2 + 2 * ε) ∧
      ∀ i, α (i + 3) = exp (-(1.98 + Real.log 4) / 2 + 3 * ε) * exp (-0.50 / 2 + ε) ^ i := by
  obtain ⟨ε, hε0, hε, hsum⟩ := decomp338_case_four_perturbation η hη
  have hlog4 : (0.34 : ℝ) ≤ Real.log 4 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_gt_d9]
  let q := exp (-0.50 / 2 + ε)
  let α : ℕ → ℝ := fun i => if i = 0 then 1 else if i = 1 then exp (-0.90 + 2 * ε)
    else if i = 2 then exp (-(1.46 + Real.log 4) / 2 + 2 * ε)
    else exp (-(1.98 + Real.log 4) / 2 + 3 * ε) * q ^ (i - 3)
  have hq : q < 1 := exp_lt_one_iff.mpr (by linarith)
  have hq0 : 0 ≤ q := (exp_pos _).le
  have hpos (i : ℕ) : 0 < α i := by
    dsimp [α]
    split_ifs <;> positivity
  have hmono (i : ℕ) : α (i + 1) ≤ α i := by
    rcases i with _ | i
    · simpa [α] using exp_le_one_iff.mpr (show -0.90 + 2 * ε ≤ 0 by linarith)
    rcases i with _ | i
    · simp only [Nat.zero_add]
      change exp (-(1.46 + Real.log 4) / 2 + 2 * ε) ≤ exp (-0.90 + 2 * ε)
      exact exp_le_exp.mpr (by linarith)
    rcases i with _ | i
    · change exp (-(1.98 + Real.log 4) / 2 + 3 * ε) * q ^ 0 ≤ exp (-(1.46 + Real.log 4) / 2 + 2 * ε)
      rw [pow_zero, mul_one]
      exact exp_le_exp.mpr (by linarith)
    · have hne0 : i + 1 + 1 + 1 ≠ 0 := by omega
      have hne1 : i + 1 + 1 + 1 ≠ 1 := by omega
      have hne2 : i + 1 + 1 + 1 ≠ 2 := by omega
      have hne0' : i + 1 + 1 + 1 + 1 ≠ 0 := by omega
      have hne1' : i + 1 + 1 + 1 + 1 ≠ 1 := by omega
      have hne2' : i + 1 + 1 + 1 + 1 ≠ 2 := by omega
      simp only [α, ite_eq_right hne0, ite_eq_right hne1, ite_eq_right hne2,
        ite_eq_right hne0', ite_eq_right hne1', ite_eq_right hne2']
      rw [show i + 1 + 1 + 1 - 3 = i by omega,
        show i + 1 + 1 + 1 + 1 - 3 = i + 1 by omega, pow_succ]
      nlinarith [mul_le_mul_of_nonneg_left hq.le
        (show 0 ≤ exp (-(1.98 + Real.log 4) / 2 + 3 * ε) * q ^ i by positivity)]
  have hshift (i : ℕ) : α (i + 1) = if i = 0 then exp (-0.90 + 2 * ε)
      else if i = 1 then exp (-(1.46 + Real.log 4) / 2 + 2 * ε)
      else exp (-(1.98 + Real.log 4) / 2 + 3 * ε) * q ^ (i - 2) := by
    by_cases hi0 : i = 0
    · subst i
      norm_num [α]
    by_cases hi1 : i = 1
    · subst i
      norm_num [α]
    have h2 : i + 1 ≠ 2 := by omega
    simp [α, hi0, hi1, h2, show i + 1 - 3 = i - 2 by omega]
  refine ⟨ε, α, hε0, hε, by simp [α], hpos, hmono, ?_, by simp [α], by simp [α], ?_⟩
  · intro n
    simp_rw [hshift]
    exact (decomp338_case_four_geometric_sum ε hε n).trans hsum.le
  · intro i
    have h1 : i + 3 ≠ 1 := by omega
    have h2 : i + 3 ≠ 2 := by omega
    simp [α, h1, h2, show i + 3 - 3 = i by omega, q]

lemma decomp338_profile_from_two (h Y t : ℕ) (hY : 4 ≤ Y) (hYt : Y ≤ t)
    (ε : ℝ) (α : ℕ → ℝ)
    (hsmall : ∀ y : ℕ, Y ≤ y → 2 / (y : ℝ) ≤ ε ∧ 28 / Real.log y ≤ ε)
    (hfirst : (decomp338GreedyCutoff h Y t 0 : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α 1)))
    (hsecond : (decomp338GreedyCutoff h Y t 1 : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α 2)))
    (hrec : ∀ i, α (i + 3) = α (i + 2) * exp (-(decomp305HeadMass (i + 2) : ℝ) / 100 / 2 + ε))
    (i : ℕ) :
    (decomp338GreedyCutoff h Y t i : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α (i + 1))) := by
  let c := decomp338GreedyCutoff h Y t
  have hlo := (decomp338_greedy_cutoff_bounds h Y t hYt).2.1
  have htail (k : ℕ) : (c (k + 1) : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α (k + 2))) := by
    induction k with
    | zero => exact hsecond
    | succ i ih =>
      change (c (i + 2) : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α (i + 3)))
      by_cases hp : (t : ℝ) ^ (α (i + 2)) ≤ Y
      · have hci : (c (i + 1) : ℝ) ≤ Y := by simpa only [max_eq_left hp] using ih
        have hs : (c (i + 2) : ℝ) ≤ c (i + 1) := by
          exact_mod_cast decomp338_greedy_step_le h Y (c (i + 1)) (i + 2)
        exact hs.trans (hci.trans (le_max_left _ _))
      · have hci : (c (i + 1) : ℝ) ≤ (t : ℝ) ^ (α (i + 2)) := by
          simpa only [max_eq_right (le_of_lt (lt_of_not_ge hp))] using ih
        let r := exp (-(decomp305HeadMass (i + 2) : ℝ) / 100 / 2 + ε)
        have hstep := decomp338_greedy_step_power_max h Y (c (i + 1)) (i + 2) hY (hlo (i + 1)) ε hsmall
        change (c (i + 2) : ℝ) ≤ max (Y : ℝ) ((c (i + 1) : ℝ) ^ r) at hstep
        have hrpow : (c (i + 1) : ℝ) ^ r ≤ ((t : ℝ) ^ (α (i + 2))) ^ r :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hci (exp_pos _).le
        have heq : ((t : ℝ) ^ (α (i + 2))) ^ r = (t : ℝ) ^ (α (i + 3)) := by
          rw [← Real.rpow_mul (Nat.cast_nonneg _), hrec i]
        exact hstep.trans (max_le_max_left _ (hrpow.trans_eq heq))
  cases i with
  | zero => exact hfirst
  | succ i => exact htail i

/-- Auxiliary later recurrence for the distinct case four profile.
First memoir page 89 case four and second memoir page 115 after 31.3 and 31.4. -/

lemma decomp338_case_four_profile_recurrence (ε : ℝ) (α : ℕ → ℝ)
    (hα2 : α 2 = exp (-(1.46 + Real.log 4) / 2 + 2 * ε))
    (htail : ∀ i, α (i + 3) = exp (-(1.98 + Real.log 4) / 2 + 3 * ε) * exp (-0.50 / 2 + ε) ^ i) :
    ∀ i, α (i + 3) = α (i + 2) * exp (-(decomp305HeadMass (i + 2) : ℝ) / 100 / 2 + ε) := by
  intro i
  cases i with
  | zero =>
    have h3 := htail 0
    norm_num only [Nat.zero_add, pow_zero, mul_one] at h3 ⊢
    rw [h3, hα2, ← exp_add]
    congr 1
    norm_num [decomp305HeadMass] <;> ring
  | succ i =>
    change α (i + 4) = α (i + 3) * _
    rw [show i + 4 = (i + 1) + 3 by omega, htail (i + 1), htail i, pow_succ]
    norm_num [decomp305HeadMass] <;> ring

theorem decomp338_mixed_support_3_15_proved :
    ∃ Y₀ : ℕ, 4 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ δ κ : ℝ, 1 / ((3 : ℝ) + 1) < δ ∧ δ ≤ 1 / 2 ∧
        1 / ((15 : ℝ) + 1) < δ * (1 / 4 : ℝ) ∧ 0 < κ ∧
        ∃ X : ℕ, ∀ ξ h : ℕ, X ≤ ξ →
          let t := ⌊(ξ : ℝ) ^ δ⌋₊
          let v := ⌊(t : ℝ) ^ (1 / 4 : ℝ)⌋₊
          let H := decomp338EncodedGap h v t
          ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
            (S.filter (fun p : ℕ => decomp338GreedyCutoff H Y t j < p)).card ≤ 2 * j + 1) →
              ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (ξ : ℝ) ^ (1 - κ) := by
  let r : ℝ := 1 / 4
  let τ := exp (-0.90 : ℝ) + exp (-(Real.log (4 : ℝ)) / 2) *
    (exp (-1.46 / 2) + exp (-1.98 / 2) / (1 - exp (-0.50 / 2)))
  obtain ⟨ε, α, hε0, hε, hα0, hαpos, hαmono, hαsum, hα1, hα2, htail⟩ :=
    decomp338_case_four_support_profile 0.001 (by norm_num)
  have hrec := decomp338_case_four_profile_recurrence ε α hα2 htail
  have hm := decompJ365_first_four_saved_exponents
  dsimp only at hm
  obtain ⟨δ₀, κ, hδ₀, hκ, hδA₀, hδB₀, hsave₀⟩ := hm.2.2.2
  let δ := min δ₀ (1 / 2)
  have hδA : (1 / 4 : ℝ) < δ := lt_min hδA₀ (by norm_num)
  have hδ0 : 0 < δ := by linarith
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hδB : (1 / 16 : ℝ) < δ * r := by dsimp [r]; nlinarith
  have hden : 0 < 1 - exp (-0.50 / 2 : ℝ) := sub_pos.mpr (exp_lt_one_iff.mpr (by norm_num))
  have hτ0 : 0 ≤ τ := by dsimp [τ]; positivity
  have hsave : δ * (1 + 2 * (τ + 0.001)) ≤ 1 - κ := by
    apply (mul_le_mul_of_nonneg_right (min_le_left δ₀ (1 / 2)) (by positivity)).trans
    convert hsave₀ using 1 <;> ring
  obtain ⟨Z, hZ, hsmall₀⟩ := decomp338_endpoint_error_threshold (ε / 2) (by positivity)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp
    (decomp338_case_four_high_mass_eventually r (by norm_num [r]) (by norm_num [r]))
  let Y₀ := max Z 100
  refine ⟨Y₀, by dsimp [Y₀]; omega, ?_⟩
  intro Y hY
  have hZY : Z ≤ Y := by dsimp [Y₀] at hY; omega
  have hY100 : 100 ≤ Y := by dsimp [Y₀] at hY; omega
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp
    (decomp338_nested_floor_cutoff 1 r 0.249 (by norm_num) le_rfl
      (by norm_num [r]) (by norm_num [r]) (by norm_num) (by norm_num [r]) Y)
  let T := max T₁ T₂
  refine ⟨δ, κ / 2, by convert hδA using 1 <;> norm_num, hδhalf, by convert hδB using 1 <;> norm_num [r], by positivity, ?_⟩
  let C : ℕ := ∏ p ∈ Nat.primesLE Y, p
  have hCpos : 0 < C := by
    apply prod_pos
    intro p hp
    exact (Nat.mem_primesLE.mp hp).2.pos
  have hcast : Tendsto (fun ξ : ℕ => (ξ : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hδ0).comp hcast).eventually
      (eventually_ge_atTop ((max (max Y 2) T : ℕ) : ℝ)))
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (show 0 < κ / 2 by positivity)).comp hcast).eventually
      (eventually_ge_atTop (C : ℝ)))
  refine ⟨max 2 (max X₁ X₂), ?_⟩
  intro ξ h hξ
  dsimp only
  let t := ⌊(ξ : ℝ) ^ δ⌋₊
  let v := ⌊(t : ℝ) ^ r⌋₊
  let H := decomp338EncodedGap h v t
  intro S hS hcaps
  change S ⊆ Nat.primesLE t at hS
  change ∀ j ∈ range (t + 1),
    (S.filter (fun p : ℕ => decomp338GreedyCutoff H Y t j < p)).card ≤ 2 * j + 1 at hcaps
  have hξ2 : 2 ≤ ξ := by omega
  have hξ0 : (0 : ℝ) < ξ := by exact_mod_cast (by omega : 0 < ξ)
  have hξ1 : (1 : ℝ) ≤ ξ := by exact_mod_cast (by omega : 1 ≤ ξ)
  have htm : max (max Y 2) T ≤ t := Nat.le_floor (hX₁ ξ (by omega))
  have hYt : Y ≤ t := by omega
  have hY4 : 4 ≤ Y := by omega
  have ht2 : 2 ≤ t := by omega
  have hsmall42 : ∀ y : ℕ, Y ≤ y → 4 / (y : ℝ) ≤ ε ∧ 42 / Real.log y ≤ ε := by
    intro y hy
    obtain ⟨h1, h2⟩ := hsmall₀ y (hZY.trans hy)
    have he1 : 4 / (y : ℝ) = 2 * (2 / (y : ℝ)) := by ring
    have he2 : 42 / Real.log y = (3 / 2 : ℝ) * (28 / Real.log y) := by ring
    constructor <;> nlinarith
  have hsmall : ∀ y : ℕ, Y ≤ y → 2 / (y : ℝ) ≤ ε ∧ 28 / Real.log y ≤ ε := by
    intro y hy
    obtain ⟨h1, h2⟩ := hsmall₀ y (hZY.trans hy)
    constructor <;> linarith
  have hsmall14 : ∀ y : ℕ, Y ≤ y → 2 / (y : ℝ) ≤ ε ∧ 14 / Real.log y ≤ ε := by
    intro y hy
    obtain ⟨h1, h2⟩ := hsmall₀ y (hZY.trans hy)
    have he : 14 / Real.log y = (1 / 2 : ℝ) * (28 / Real.log y) := by ring
    constructor <;> nlinarith
  have hhigh := hT₁ t (by dsimp [T] at htm; omega)
  have hvlarge := hT₂ t (by dsimp [T] at htm; omega)
  simp only [Real.rpow_one, Nat.floor_natCast] at hvlarge
  have hYv : Y ≤ v := hvlarge.1
  have hvt : v ≤ t := hhigh.2.1
  have hshift : Real.log 4 ≤ Real.log (Real.log t / Real.log v) := by
    have hh := hhigh.2.2.2
    dsimp [r] at hh
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, Real.log_inv, neg_neg] at hh
    simpa only [v, r, one_div] using hh
  have hfirst : (decomp338GreedyCutoff H Y t 0 : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α 1)) := by
    rw [hα1]
    exact decomp338_case_four_first_power h Y v t hY4 hYv hvt
      (Nat.floor_le (by positivity)) ε hε0.le hsmall14
  have hsecond : (decomp338GreedyCutoff H Y t 1 : ℝ) ≤ max (Y : ℝ) ((t : ℝ) ^ (α 2)) := by
    rw [hα2]
    apply decomp338_mixed_second_power_max h Y v t hY100 hYv hvt (2 * ε) (Real.log 4) hhigh.2.2.1
    · intro y hy
      obtain ⟨h1, h2⟩ := hsmall42 y hy
      constructor <;> linarith
    · exact hshift
  have hprofile := decomp338_profile_from_two H Y t hY4 hYt ε α hsmall hfirst hsecond hrec
  have hstop := decomp338_greedy_stops H Y t hY4 hYt
  let A := S.filter (fun p => Y < p)
  let B := S.filter (fun p => p ≤ Y)
  have hAB : S = A ∪ B := by
    ext p
    simp only [A, B, mem_filter, mem_union]
    constructor
    · intro hp
      by_cases hy : Y < p
      · exact Or.inl ⟨hp, hy⟩
      · exact Or.inr ⟨hp, by omega⟩
    · intro hp
      rcases hp with hp | hp <;> exact hp.1
  have hdisj : Disjoint A B := by
    apply disjoint_left.mpr
    intro p hp hq
    have hpY := (mem_filter.mp hp).2
    have hqY := (mem_filter.mp hq).2
    omega
  have hBsub : B ⊆ Nat.primesLE Y := by
    intro p hp
    obtain ⟨hpS, hpY⟩ := mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpY, (Nat.mem_primesLE.mp (hS hpS)).2⟩
  have hBbound : (∏ p ∈ B, p) ≤ C :=
    Nat.le_of_dvd hCpos (prod_dvd_prod_of_subset B (Nat.primesLE Y) id hBsub)
  have hcard : A.card ≤ 2 * t + 1 := by
    have hh := hcaps t (mem_range.mpr (by omega : t < t + 1))
    simpa only [hstop] using hh
  have hAcaps : ∀ i ∈ range t,
      (A.filter (fun p : ℕ => (t : ℝ) ^ (α (i + 1)) < (p : ℝ))).card ≤ 2 * i + 1 := by
    intro i hi
    have hsub : A.filter (fun p : ℕ => (t : ℝ) ^ (α (i + 1)) < (p : ℝ)) ⊆
        S.filter (fun p : ℕ => decomp338GreedyCutoff H Y t i < p) := by
      intro p hp
      obtain ⟨hpA, hpow⟩ := mem_filter.mp hp
      obtain ⟨hpS, hpY⟩ := mem_filter.mp hpA
      have hpYR : (Y : ℝ) < p := by exact_mod_cast hpY
      have hmax : max (Y : ℝ) ((t : ℝ) ^ (α (i + 1))) < p := max_lt_iff.mpr ⟨hpYR, hpow⟩
      have hcR := (hprofile i).trans_lt hmax
      exact mem_filter.mpr ⟨hpS, by exact_mod_cast hcR⟩
    exact (card_le_card hsub).trans (hcaps i (mem_range.mpr (by have := mem_range.mp hi; omega)))
  have htop : (t : ℝ) ≤ (ξ : ℝ) ^ δ := Nat.floor_le (by positivity)
  have hApos : ∀ p ∈ A, 0 < p := by
    intro p hp
    exact (Nat.mem_primesLE.mp (hS (mem_filter.mp hp).1)).2.pos
  have hAmax : ∀ p ∈ A, (p : ℝ) ≤ t := by
    intro p hp
    exact_mod_cast (Nat.mem_primesLE.mp (hS (mem_filter.mp hp).1)).1
  have hτ : 0 ≤ τ + 0.001 := by
    simpa using hαsum 0
  have hlarge := decompJ365_nested_saved_support A ξ t δ
    (τ + 0.001) κ hξ1
    (by exact_mod_cast (by omega : 1 < t)) htop hτ hκ α hαmono hα0 t
    (hαpos t).le (hαsum t) hApos hAmax hcard hAcaps hsave
  have hsmallprod : ((∏ p ∈ B, p : ℕ) : ℝ) ≤ C := by exact_mod_cast hBbound
  have hCbound : (C : ℝ) ≤ (ξ : ℝ) ^ (κ / 2) := hX₂ ξ (by omega)
  have hsplit : ((∏ p ∈ S, p : ℕ) : ℝ) =
      ((∏ p ∈ A, p : ℕ) : ℝ) * ((∏ p ∈ B, p : ℕ) : ℝ) := by
    rw [hAB, prod_union hdisj, Nat.cast_mul]
  calc
    _ = ((∏ p ∈ A, p : ℕ) : ℝ) * ((∏ p ∈ B, p : ℕ) : ℝ) := hsplit
    _ ≤ (ξ : ℝ) ^ (1 - κ) * (C : ℝ) :=
      mul_le_mul hlarge hsmallprod (Nat.cast_nonneg _) (Real.rpow_nonneg hξ0.le _)
    _ ≤ (ξ : ℝ) ^ (1 - κ) * (ξ : ℝ) ^ (κ / 2) :=
      mul_le_mul_of_nonneg_left hCbound (Real.rpow_nonneg hξ0.le _)
    _ = (ξ : ℝ) ^ (1 - κ / 2) := by
      rw [← Real.rpow_add hξ0]
      congr 1
      ring

theorem decomp338_mixed_z_finite (a b ξ N t v : ℕ) (m : ℤ) (hv : 2 ≤ v) (hvt : v ≤ t)
    (hN : N + 2 * m.natAbs ≤ ξ + 1)
    (hsizeA : (ξ : ℝ) < (t : ℝ) ^ (a + 1)) (hsizeB : (ξ : ℝ) < (v : ℝ) ^ (b + 1))
    (hthA : (ξ : ℝ) ^ (1 / ((a : ℝ) + 1)) ≤ t)
    (hthB : (ξ : ℝ) ^ (1 / ((b : ℝ) + 1)) ≤ v)
    (J : Finset ℕ) (cutoff level : ℕ → ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hlevel : ∀ S ⊆ Nat.primesLE t, (∀ j ∈ J,
      (S.filter (fun p : ℕ => cutoff j < p)).card ≤ 2 * level j + 1) →
        ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L) :
    let H := decomp338EncodedGap (2 * m.natAbs) v t
    let U := (Nat.primesLE t).powerset.filter (fun S => ∀ j ∈ J,
      (S.filter (fun p : ℕ => cutoff j < p)).card ≤ 2 * level j + 1)
    (N : ℝ) * (∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN H p) -
      L * (1 + Real.log L) ^ 2 ≤ zCount a b m ξ := by
  exact decomp338_mixed_z_finite_proved a b ξ N t v m hv hvt hN hsizeA hsizeB hthA hthB
    J cutoff level L hL hlevel

/-- LEAF. First memoir pages 88 and 89, second memoir pages 106, 107 and 115.
Auxiliary finite mixed CRT Brun inequality for W, with its actual count and explicit level error.
The density encoding is used only in the main coefficients. -/

theorem decomp338_mixed_w_finite (a b N t v : ℕ) (hv : 2 ≤ v) (hvt : v ≤ t)
    (hthA : (N : ℝ) ^ (1 / ((a : ℝ) + 1)) ≤ t)
    (hthB : (N : ℝ) ^ (1 / ((b : ℝ) + 1)) ≤ v)
    (J : Finset ℕ) (cutoff level : ℕ → ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hlevel : ∀ S ⊆ Nat.primesLE t, (∀ j ∈ J,
      (S.filter (fun p : ℕ => cutoff j < p)).card ≤ 2 * level j + 1) →
        ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L) :
    let H := decomp338EncodedGap N v t
    let U := (Nat.primesLE t).powerset.filter (fun S => ∀ j ∈ J,
      (S.filter (fun p : ℕ => cutoff j < p)).card ≤ 2 * level j + 1)
    (N : ℝ) * (∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN H p) -
      L * (1 + Real.log L) ^ 2 ≤ wCount a b N := by
  exact decomp338_mixed_w_finite_proved a b N t v hv hvt hthA hthB J cutoff level L hL hlevel

/-- LEAF. First memoir page 89 and second memoir pages 113 to 115.
First memoir page 89 case two, the tau bar display, and second memoir page 115 after 31.3 and 31.4.
Auxiliary mixed saved support for 5 and 7 at omega equal to log of four thirds.
This bounds only retained prime products and contains no integer count. -/

theorem decomp338_mixed_support_5_7 :
    ∃ Y₀ : ℕ, 4 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ δ κ : ℝ, 1 / ((5 : ℝ) + 1) < δ ∧ δ ≤ 1 / 2 ∧
        1 / ((7 : ℝ) + 1) < δ * (3 / 4 : ℝ) ∧ 0 < κ ∧
        ∃ X : ℕ, ∀ ξ h : ℕ, X ≤ ξ →
          let t := ⌊(ξ : ℝ) ^ δ⌋₊
          let v := ⌊(t : ℝ) ^ (3 / 4 : ℝ)⌋₊
          let H := decomp338EncodedGap h v t
          ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
            (S.filter (fun p : ℕ => decomp338GreedyCutoff H Y t j < p)).card ≤ 2 * j + 1) →
              ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (ξ : ℝ) ^ (1 - κ) := by
  exact decomp338_mixed_support_5_7_proved

/-- LEAF. First memoir page 89 and second memoir pages 113 to 115.
First memoir page 89 case three, the tau bar display, and second memoir page 115 after 31.3 and 31.4.
Auxiliary mixed saved support for 4 and 9 at omega equal to log of two.
This bounds only retained prime products and contains no integer count. -/

theorem decomp338_mixed_support_4_9 :
    ∃ Y₀ : ℕ, 4 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ δ κ : ℝ, 1 / ((4 : ℝ) + 1) < δ ∧ δ ≤ 1 / 2 ∧
        1 / ((9 : ℝ) + 1) < δ * (1 / 2 : ℝ) ∧ 0 < κ ∧
        ∃ X : ℕ, ∀ ξ h : ℕ, X ≤ ξ →
          let t := ⌊(ξ : ℝ) ^ δ⌋₊
          let v := ⌊(t : ℝ) ^ (1 / 2 : ℝ)⌋₊
          let H := decomp338EncodedGap h v t
          ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
            (S.filter (fun p : ℕ => decomp338GreedyCutoff H Y t j < p)).card ≤ 2 * j + 1) →
              ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (ξ : ℝ) ^ (1 - κ) := by
  exact decomp338_mixed_support_4_9_proved

/-- LEAF. First memoir page 89 and second memoir pages 113 to 115.
First memoir page 89 case four, the tau bar display, and second memoir page 115 after 31.3 and 31.4.
Auxiliary mixed saved support for 3 and 15 at omega equal to log of four.
This bounds only retained prime products and contains no integer count. -/

theorem decomp338_mixed_support_3_15 :
    ∃ Y₀ : ℕ, 4 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ δ κ : ℝ, 1 / ((3 : ℝ) + 1) < δ ∧ δ ≤ 1 / 2 ∧
        1 / ((15 : ℝ) + 1) < δ * (1 / 4 : ℝ) ∧ 0 < κ ∧
        ∃ X : ℕ, ∀ ξ h : ℕ, X ≤ ξ →
          let t := ⌊(ξ : ℝ) ^ δ⌋₊
          let v := ⌊(t : ℝ) ^ (1 / 4 : ℝ)⌋₊
          let H := decomp338EncodedGap h v t
          ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
            (S.filter (fun p : ℕ => decomp338GreedyCutoff H Y t j < p)).card ≤ 2 * j + 1) →
              ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (ξ : ℝ) ^ (1 - κ) := by
  exact decomp338_mixed_support_3_15_proved

/-- CONDITIONAL ON the supplied mixed saved support. The finite Z sieve is proved.
Auxiliary complete assembly of a mixed lower Z count, first memoir pages 75, 88 and 89. -/

lemma decomp338_mixed_Z_of_support (a b : ℕ) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hsupport : ∃ Y₀ : ℕ, 4 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ δ κ : ℝ, 1 / ((a : ℝ) + 1) < δ ∧ δ ≤ 1 / 2 ∧
        1 / ((b : ℝ) + 1) < δ * r ∧ 0 < κ ∧
        ∃ X : ℕ, ∀ ξ h : ℕ, X ≤ ξ →
          let t := ⌊(ξ : ℝ) ^ δ⌋₊
          let v := ⌊(t : ℝ) ^ r⌋₊
          let H := decomp338EncodedGap h v t
          ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
            (S.filter (fun p : ℕ => decomp338GreedyCutoff H Y t j < p)).card ≤ 2 * j + 1) →
              ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (ξ : ℝ) ^ (1 - κ)) :
    ∀ m : ℤ, m ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℕ, ∀ ξ : ℕ, ξ₀ ≤ ξ →
      c * ξ / Real.log ξ ^ 2 ≤ zCount a b m ξ := by
  intro m hm
  obtain ⟨Y₁, hY₁, hmain⟩ := decomp338_greedy_main_proved
  obtain ⟨Y₂, hY₂, hsupp⟩ := hsupport
  let Y := max Y₁ Y₂
  obtain ⟨a₀, ha₀, T, hmain⟩ := hmain Y (le_max_left _ _)
  obtain ⟨δ, κ, hδA, hδhalf, hδB, hκ, X, hsupp⟩ := hsupp Y (le_max_right _ _)
  have hδ : 0 < δ := lt_trans (by positivity : (0 : ℝ) < 1 / ((a : ℝ) + 1)) hδA
  let A : ℝ := (1 + |1 - κ|) ^ 2
  let B : ℝ := a₀ * exp (-52 : ℝ) / 4
  have hB : 0 < B := by dsimp [B]; positivity
  apply decompJ365_lower_of_main_error hB (show 0 < κ / 2 by positivity) A
  have hcutA := decomp338_nested_floor_cutoff δ 1 (1 / ((a : ℝ) + 1)) hδ (by linarith)
    (by norm_num) (by norm_num) (by positivity) (by simpa using hδA) (max T 3)
  have hcutB := decomp338_nested_floor_cutoff δ r (1 / ((b : ℝ) + 1)) hδ (by linarith)
    hr hr1 (by positivity) hδB 3
  filter_upwards [hcutA, hcutB, decomp338_level_error_upper κ hκ, eventually_ge_atTop X,
    eventually_ge_atTop (max 3 (4 * m.natAbs))] with ξ hA hBb herr hX hξ
  let t := ⌊(ξ : ℝ) ^ δ⌋₊
  let v := ⌊(t : ℝ) ^ r⌋₊
  let H := decomp338EncodedGap (2 * m.natAbs) v t
  let N := ξ + 1 - 2 * m.natAbs
  let L := (ξ : ℝ) ^ (1 - κ)
  let c := decomp338GreedyCutoff H Y t
  let U := (Nat.primesLE t).powerset.filter (fun S =>
    ∀ j ∈ range (t + 1), (S.filter (fun p : ℕ => c j < p)).card ≤ 2 * j + 1)
  let E := ∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN H p
  have htm : max T 3 ≤ t := by simpa only [Real.rpow_one, Nat.floor_natCast] using hA.1
  have hrootA : (ξ : ℝ) ^ (1 / ((a : ℝ) + 1)) < t := by
    simpa only [Real.rpow_one, Nat.floor_natCast] using hA.2.2.2
  have hrootB : (ξ : ℝ) ^ (1 / ((b : ℝ) + 1)) < v := hBb.2.2.2
  have hvt : v ≤ t := hBb.2.1
  have hv3 : 3 ≤ v := hBb.1
  have ht3 : 3 ≤ t := by omega
  have htξ : t ≤ ξ := hA.2.2.1
  have hξR : (1 : ℝ) < ξ := by exact_mod_cast (by omega : 1 < ξ)
  have heven : Even H := decomp338_encoded_gap_even (2 * m.natAbs) v t ⟨m.natAbs, by omega⟩
  have hL : 1 ≤ L := by
    have hh := hsupp ξ (2 * m.natAbs) hX ∅ (empty_subset _) (by simp)
    simpa [L] using hh
  have hlevel : ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
      (S.filter (fun p : ℕ => c j < p)).card ≤ 2 * j + 1) → ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L :=
    hsupp ξ (2 * m.natAbs) hX
  have hraw := decomp338_mixed_z_finite a b ξ N t v m (by omega) hvt (by dsimp [N]; omega)
    (decomp338_size_of_root_lt a ξ t hrootA) (decomp338_size_of_root_lt b ξ v hrootB)
    hrootA.le hrootB.le (range (t + 1)) c id L hL hlevel
  change (N : ℝ) * E - L * (1 + Real.log L) ^ 2 ≤ zCount a b m ξ at hraw
  have hprod := decomp338_full_pair_product_lower H t heven ht3
  have hlogt : 0 < Real.log t := Real.log_pos (by exact_mod_cast (by omega : 1 < t))
  have hlogξ : 0 < Real.log ξ := Real.log_pos hξR
  have hlogle : Real.log t ≤ Real.log ξ := Real.log_le_log (by exact_mod_cast (by omega : 0 < t))
    (by exact_mod_cast htξ)
  have hprod' : exp (-52 : ℝ) / (2 * Real.log ξ ^ 2) ≤
      ∏ p ∈ Nat.primesLE t, (1 - nuN H p) := by
    apply le_trans _ hprod
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  have hE : a₀ * exp (-52 : ℝ) / (2 * Real.log ξ ^ 2) ≤ E := by
    have hh := hmain H t heven (by omega)
    change a₀ * (∏ p ∈ Nat.primesLE t, (1 - nuN H p)) ≤ E at hh
    calc
      _ = a₀ * (exp (-52 : ℝ) / (2 * Real.log ξ ^ 2)) := by ring
      _ ≤ a₀ * (∏ p ∈ Nat.primesLE t, (1 - nuN H p)) := mul_le_mul_of_nonneg_left hprod' ha₀.le
      _ ≤ E := hh
  have hN : (ξ : ℝ) / 2 ≤ N := by
    have hn : ξ ≤ 2 * N := by dsimp [N]; omega
    have hnR : (ξ : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hn
    linarith
  have hmainterm : B * ξ / Real.log ξ ^ 2 ≤ (N : ℝ) * E := by
    calc
      _ = ((ξ : ℝ) / 2) * (a₀ * exp (-52 : ℝ) / (2 * Real.log ξ ^ 2)) := by dsimp [B]; ring
      _ ≤ (N : ℝ) * (a₀ * exp (-52 : ℝ) / (2 * Real.log ξ ^ 2)) := by gcongr
      _ ≤ (N : ℝ) * E := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _)
  change L * (1 + Real.log L) ^ 2 ≤ A * (ξ : ℝ) ^ (1 - κ / 2) at herr
  linarith

/-- CONDITIONAL ON the supplied mixed saved support.
Auxiliary complete assembly of a mixed lower W count, first memoir pages 88 and 89. -/

lemma decomp338_mixed_W_of_support (a b : ℕ) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hsupport : ∃ Y₀ : ℕ, 4 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ δ κ : ℝ, 1 / ((a : ℝ) + 1) < δ ∧ δ ≤ 1 / 2 ∧
        1 / ((b : ℝ) + 1) < δ * r ∧ 0 < κ ∧
        ∃ X : ℕ, ∀ ξ h : ℕ, X ≤ ξ →
          let t := ⌊(ξ : ℝ) ^ δ⌋₊
          let v := ⌊(t : ℝ) ^ r⌋₊
          let H := decomp338EncodedGap h v t
          ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
            (S.filter (fun p : ℕ => decomp338GreedyCutoff H Y t j < p)).card ≤ 2 * j + 1) →
              ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (ξ : ℝ) ^ (1 - κ)) :
    TheoremDW a b := by
  obtain ⟨Y₁, hY₁, hmain⟩ := decomp338_greedy_main_proved
  obtain ⟨Y₂, hY₂, hsupp⟩ := hsupport
  let Y := max Y₁ Y₂
  obtain ⟨a₀, ha₀, T, hmain⟩ := hmain Y (le_max_left _ _)
  obtain ⟨δ, κ, hδA, hδhalf, hδB, hκ, X, hsupp⟩ := hsupp Y (le_max_right _ _)
  have hδ : 0 < δ := lt_trans (by positivity : (0 : ℝ) < 1 / ((a : ℝ) + 1)) hδA
  let A : ℝ := (1 + |1 - κ|) ^ 2
  let B : ℝ := a₀ * exp (-52 : ℝ) / 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hcutA := decomp338_nested_floor_cutoff δ 1 (1 / ((a : ℝ) + 1)) hδ (by linarith)
    (by norm_num) (by norm_num) (by positivity) (by simpa using hδA) (max T 3)
  have hcutB := decomp338_nested_floor_cutoff δ r (1 / ((b : ℝ) + 1)) hδ (by linarith)
    hr hr1 (by positivity) hδB 3
  have hbound : ∀ᶠ N : ℕ in atTop, Even N →
      B * N / Real.log N ^ 2 - A * (N : ℝ) ^ (1 - κ / 2) ≤ wCount a b N := by
    filter_upwards [hcutA, hcutB, decomp338_level_error_upper κ hκ,
      eventually_ge_atTop X, eventually_ge_atTop 3] with N hA hBb herr hX hN
    intro hevenN
    let t := ⌊(N : ℝ) ^ δ⌋₊
    let v := ⌊(t : ℝ) ^ r⌋₊
    let H := decomp338EncodedGap N v t
    let L := (N : ℝ) ^ (1 - κ)
    let c := decomp338GreedyCutoff H Y t
    let U := (Nat.primesLE t).powerset.filter (fun S =>
      ∀ j ∈ range (t + 1), (S.filter (fun p : ℕ => c j < p)).card ≤ 2 * j + 1)
    let E := ∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN H p
    have htm : max T 3 ≤ t := by simpa only [Real.rpow_one, Nat.floor_natCast] using hA.1
    have hrootA : (N : ℝ) ^ (1 / ((a : ℝ) + 1)) < t := by
      simpa only [Real.rpow_one, Nat.floor_natCast] using hA.2.2.2
    have hrootB : (N : ℝ) ^ (1 / ((b : ℝ) + 1)) < v := hBb.2.2.2
    have hvt : v ≤ t := hBb.2.1
    have hv3 : 3 ≤ v := hBb.1
    have ht3 : 3 ≤ t := by omega
    have htN : t ≤ N := hA.2.2.1
    have hNR : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    have heven : Even H := decomp338_encoded_gap_even N v t hevenN
    have hL : 1 ≤ L := by
      have hh := hsupp N N hX ∅ (empty_subset _) (by simp)
      simpa [L] using hh
    have hlevel : ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
        (S.filter (fun p : ℕ => c j < p)).card ≤ 2 * j + 1) → ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L :=
      hsupp N N hX
    have hraw := decomp338_mixed_w_finite a b N t v (by omega) hvt hrootA.le hrootB.le
      (range (t + 1)) c id L hL hlevel
    change (N : ℝ) * E - L * (1 + Real.log L) ^ 2 ≤ wCount a b N at hraw
    have hprod := decomp338_full_pair_product_lower H t heven ht3
    have hlogt : 0 < Real.log t := Real.log_pos (by exact_mod_cast (by omega : 1 < t))
    have hlogN : 0 < Real.log N := Real.log_pos hNR
    have hlogle : Real.log t ≤ Real.log N := Real.log_le_log (by exact_mod_cast (by omega : 0 < t))
      (by exact_mod_cast htN)
    have hprod' : exp (-52 : ℝ) / (2 * Real.log N ^ 2) ≤
        ∏ p ∈ Nat.primesLE t, (1 - nuN H p) := by
      apply le_trans _ hprod
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    have hE : a₀ * exp (-52 : ℝ) / (2 * Real.log N ^ 2) ≤ E := by
      have hh := hmain H t heven (by omega)
      change a₀ * (∏ p ∈ Nat.primesLE t, (1 - nuN H p)) ≤ E at hh
      calc
        _ = a₀ * (exp (-52 : ℝ) / (2 * Real.log N ^ 2)) := by ring
        _ ≤ a₀ * (∏ p ∈ Nat.primesLE t, (1 - nuN H p)) := mul_le_mul_of_nonneg_left hprod' ha₀.le
        _ ≤ E := hh
    have hmainterm : B * N / Real.log N ^ 2 ≤ (N : ℝ) * E := by
      calc
        _ = (N : ℝ) * (a₀ * exp (-52 : ℝ) / (2 * Real.log N ^ 2)) := by dsimp [B]; ring
        _ ≤ (N : ℝ) * E := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _)
    change L * (1 + Real.log L) ^ 2 ≤ A * (N : ℝ) ^ (1 - κ / 2) at herr
    linarith
  have hfinal : ∀ᶠ N : ℕ in atTop, Even N → (B / 2) * N / Real.log N ^ 2 ≤ wCount a b N := by
    filter_upwards [hbound, decompJ365_power_error_absorb (show 0 < κ / 2 by positivity) hB A]
      with N hN herr
    intro heven
    have hh := hN heven
    have heq : B * N / Real.log N ^ 2 = 2 * ((B / 2) * N / Real.log N ^ 2) := by ring
    linarith
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hfinal
  exact ⟨B / 2, by positivity, N₀, fun N hN heven => hN₀ N hN heven⟩

/-- Clean supplier from the proved finite Z sieve and shifted support.
Exact lower Z leaf assembly from first memoir pages 75, 88 and 89. -/

theorem decomp338_Z_lower_5_7 :
    ∀ m : ℤ, m ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℕ, ∀ ξ : ℕ, ξ₀ ≤ ξ →
      c * ξ / Real.log ξ ^ 2 ≤ zCount 5 7 m ξ := by
  exact decomp338_mixed_Z_of_support 5 7 (3 / 4 : ℝ) (by norm_num) (by norm_num)
    decomp338_mixed_support_5_7

/-- Clean supplier from the proved finite W sieve and shifted support.
Exact W leaf assembly from first memoir page 89. -/

theorem decomp338_W_5_7 : TheoremDW 5 7 := by
  exact decomp338_mixed_W_of_support 5 7 (3 / 4 : ℝ) (by norm_num) (by norm_num)
    decomp338_mixed_support_5_7

/-- Clean supplier from the proved finite Z sieve and shifted support.
Exact lower Z leaf assembly from first memoir pages 75, 88 and 89. -/

theorem decomp338_Z_lower_4_9 :
    ∀ m : ℤ, m ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℕ, ∀ ξ : ℕ, ξ₀ ≤ ξ →
      c * ξ / Real.log ξ ^ 2 ≤ zCount 4 9 m ξ := by
  exact decomp338_mixed_Z_of_support 4 9 (1 / 2 : ℝ) (by norm_num) (by norm_num)
    decomp338_mixed_support_4_9

/-- Clean supplier from the proved finite W sieve and shifted support.
Exact W leaf assembly from first memoir page 89. -/

theorem decomp338_W_4_9 : TheoremDW 4 9 := by
  exact decomp338_mixed_W_of_support 4 9 (1 / 2 : ℝ) (by norm_num) (by norm_num)
    decomp338_mixed_support_4_9

/-- Clean supplier from the proved finite sieve and distinct shifted support.
Exact lower Z leaf assembly from first memoir pages 75, 88 and 89. -/

theorem decomp338_Z_lower_3_15 :
    ∀ m : ℤ, m ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℕ, ∀ ξ : ℕ, ξ₀ ≤ ξ →
      c * ξ / Real.log ξ ^ 2 ≤ zCount 3 15 m ξ := by
  exact decomp338_mixed_Z_of_support 3 15 (1 / 4 : ℝ) (by norm_num) (by norm_num)
    decomp338_mixed_support_3_15

/-- Clean supplier from the proved finite sieve and distinct shifted support.
Exact W leaf assembly from first memoir page 89. -/

theorem decomp338_W_3_15 : TheoremDW 3 15 := by
  exact decomp338_mixed_W_of_support 3 15 (1 / 4 : ℝ) (by norm_num) (by norm_num)
    decomp338_mixed_support_3_15

theorem decomp338_W_6_6 : TheoremDW 6 6 := by
  obtain ⟨Y₁, hY₁, hmain⟩ := decomp338_greedy_main_proved
  obtain ⟨Y₂, hY₂, hsupp⟩ := decomp338_greedy_support_proved
  let Y := max Y₁ Y₂
  obtain ⟨a, ha, T, hmain⟩ := hmain Y (le_max_left _ _)
  obtain ⟨δ, κ, hδ, hδhalf, hκ, X, hsupp⟩ := hsupp Y (le_max_right _ _)
  let A : ℝ := (1 + |1 - κ|) ^ 2
  let B : ℝ := a * exp (-52 : ℝ) / 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound : ∀ᶠ N : ℕ in atTop, Even N →
      B * N / Real.log N ^ 2 - A * (N : ℝ) ^ (1 - κ / 2) ≤ wCount 6 6 N := by
    filter_upwards [decomp338_floor_power_cutoff δ hδ hδhalf T,
      decomp338_level_error_upper κ hκ, eventually_ge_atTop X, eventually_ge_atTop 3]
      with N hcut herr hX hN
    intro heven
    let t := ⌊(N : ℝ) ^ δ⌋₊
    let L := (N : ℝ) ^ (1 - κ)
    let c := decomp338GreedyCutoff N Y t
    let U := (Nat.primesLE t).powerset.filter (fun S =>
      ∀ j ∈ range (t + 1), (S.filter (fun p : ℕ => c j < p)).card ≤ 2 * j + 1)
    let E := ∑ S ∈ U, (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN N p
    have ht3 : 3 ≤ t := hcut.1
    have hNR : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    have hL : 1 ≤ L := by
      have hh := hsupp N N hX ∅ (empty_subset _) (by simp)
      simpa [L] using hh
    have hlevel : ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
        (S.filter (fun p : ℕ => c j < p)).card ≤ 2 * j + 1) → ((∏ p ∈ S, p : ℕ) : ℝ) ≤ L :=
      hsupp N N hX
    have hth : (N : ℝ) ^ (1 / ((6 : ℝ) + 1)) ≤ t := by
      convert hcut.2.2.2.2 using 1 <;> norm_num
    have hraw := decomp305_wCount_finite_lower 6 6 N t (by omega) hth hth
      (range (t + 1)) c id L hL hlevel
    change (N : ℝ) * E - L * (1 + Real.log L) ^ 2 ≤ wCount 6 6 N at hraw
    have hprod := decomp338_full_pair_product_lower N t heven ht3
    have hlogt : 0 < Real.log t := Real.log_pos (by exact_mod_cast (by omega : 1 < t))
    have hlogN : 0 < Real.log N := Real.log_pos hNR
    have hlogle : Real.log t ≤ Real.log N := Real.log_le_log (by exact_mod_cast (by omega : 0 < t))
      (by exact_mod_cast hcut.2.2.1)
    have hprod' : exp (-52 : ℝ) / (2 * Real.log N ^ 2) ≤
        ∏ p ∈ Nat.primesLE t, (1 - nuN N p) := by
      apply le_trans _ hprod
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith
    have hE : a * exp (-52 : ℝ) / (2 * Real.log N ^ 2) ≤ E := by
      have hh := hmain N t heven hcut.2.1
      change a * (∏ p ∈ Nat.primesLE t, (1 - nuN N p)) ≤ E at hh
      calc
        _ = a * (exp (-52 : ℝ) / (2 * Real.log N ^ 2)) := by ring
        _ ≤ a * (∏ p ∈ Nat.primesLE t, (1 - nuN N p)) := mul_le_mul_of_nonneg_left hprod' ha.le
        _ ≤ E := hh
    have hmainterm : B * N / Real.log N ^ 2 ≤ (N : ℝ) * E := by
      calc
        _ = (N : ℝ) * (a * exp (-52 : ℝ) / (2 * Real.log N ^ 2)) := by dsimp [B]; ring
        _ ≤ (N : ℝ) * E := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _)
    change L * (1 + Real.log L) ^ 2 ≤ A * (N : ℝ) ^ (1 - κ / 2) at herr
    linarith
  have hfinal : ∀ᶠ N : ℕ in atTop, Even N → (B / 2) * N / Real.log N ^ 2 ≤ wCount 6 6 N := by
    filter_upwards [hbound, decompJ365_power_error_absorb (show 0 < κ / 2 by positivity) hB A]
      with N hN herr
    intro heven
    have hh := hN heven
    have heq : B * N / Real.log N ^ 2 = 2 * ((B / 2) * N / Real.log N ^ 2) := by ring
    linarith
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hfinal
  exact ⟨B / 2, by positivity, N₀, fun N hN heven => hN₀ N hN heven⟩

/-- LEAF. Pages 75, 88 and 89: the remaining positive lower count for Z.
The upper estimate is decompJ365_zCount_upper; the lower count is decomp338_Z_lower_*,
the `Decomp305a`/`Decomp338*` chain transcribed above. -/
theorem decompJ365_Z_lower_6_6 :
    ∀ m : ℤ, m ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℕ, ∀ ξ : ℕ, ξ₀ ≤ ξ →
      c * ξ / Real.log ξ ^ 2 ≤ zCount 6 6 m ξ :=
  decomp338_Z_lower_6_6

/-- LEAF. Pages 75, 88 and 89: the remaining positive lower count for Z.
The upper estimate is decompJ365_zCount_upper; the lower count is decomp338_Z_lower_*,
the `Decomp305a`/`Decomp338*` chain transcribed above. -/
theorem decompJ365_Z_lower_5_7 :
    ∀ m : ℤ, m ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℕ, ∀ ξ : ℕ, ξ₀ ≤ ξ →
      c * ξ / Real.log ξ ^ 2 ≤ zCount 5 7 m ξ :=
  decomp338_Z_lower_5_7

/-- LEAF. Pages 75, 88 and 89: the remaining positive lower count for Z.
The upper estimate is decompJ365_zCount_upper; the lower count is decomp338_Z_lower_*,
the `Decomp305a`/`Decomp338*` chain transcribed above. -/
theorem decompJ365_Z_lower_4_9 :
    ∀ m : ℤ, m ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℕ, ∀ ξ : ℕ, ξ₀ ≤ ξ →
      c * ξ / Real.log ξ ^ 2 ≤ zCount 4 9 m ξ :=
  decomp338_Z_lower_4_9

/-- LEAF. Pages 75, 88 and 89: the remaining positive lower count for Z.
The upper estimate is decompJ365_zCount_upper; the lower count is decomp338_Z_lower_*,
the `Decomp305a`/`Decomp338*` chain transcribed above. -/
theorem decompJ365_Z_lower_3_15 :
    ∀ m : ℤ, m ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℕ, ∀ ξ : ℕ, ξ₀ ≤ ξ →
      c * ξ / Real.log ξ ^ 2 ≤ zCount 3 15 m ξ :=
  decomp338_Z_lower_3_15

/-- LEAF. Pages 75, 88 and 90: the remaining positive lower count for Z.
The upper estimate is decompJ365_zCount_upper; the lower count is decomp338_Z_lower_*,
the `Decomp305a`/`Decomp338*` chain transcribed above. -/
theorem decompJ365_Z_lower_2_366 :
    ∀ m : ℤ, m ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℕ, ∀ ξ : ℕ, ξ₀ ≤ ξ →
      c * ξ / Real.log ξ ^ 2 ≤ zCount 2 366 m ξ := by
  sorry

/-- LEAF. Page 89, the Z half of Theorem D for (6, 6). -/
theorem decompJ365_Z_6_6 : TheoremDZ 6 6 := by
  exact decompJ365_Z_of_lower decompJ365_Z_lower_6_6

/-- LEAF. Page 89, the W half of Theorem D for (6, 6). -/
theorem decompJ365_W_6_6 : TheoremDW 6 6 :=
  decomp338_W_6_6

/-- LEAF. Page 89, the Z half of Theorem D for (5, 7). -/
theorem decompJ365_Z_5_7 : TheoremDZ 5 7 := by
  exact decompJ365_Z_of_lower decompJ365_Z_lower_5_7

/-- LEAF. Page 89, the W half of Theorem D for (5, 7). -/
theorem decompJ365_W_5_7 : TheoremDW 5 7 :=
  decomp338_W_5_7

/-- LEAF. Page 89, the Z half of Theorem D for (4, 9). -/
theorem decompJ365_Z_4_9 : TheoremDZ 4 9 := by
  exact decompJ365_Z_of_lower decompJ365_Z_lower_4_9

/-- LEAF. Page 89, the W half of Theorem D for (4, 9). -/
theorem decompJ365_W_4_9 : TheoremDW 4 9 :=
  decomp338_W_4_9

/-- LEAF. Page 89, the Z half of Theorem D for (3, 15). -/
theorem decompJ365_Z_3_15 : TheoremDZ 3 15 := by
  exact decompJ365_Z_of_lower decompJ365_Z_lower_3_15

/-- LEAF. Page 89, the W half of Theorem D for (3, 15). -/
theorem decompJ365_W_3_15 : TheoremDW 3 15 :=
  decomp338_W_3_15

/-- LEAF. Page 90, the Z half of Theorem D for (2, 366). -/
theorem decompJ365_Z_2_366 : TheoremDZ 2 366 := by
  exact decompJ365_Z_of_lower decompJ365_Z_lower_2_366

/-- LEAF. Page 90, the W half of Theorem D for (2, 366). -/
theorem decompJ365_W_2_366 : TheoremDW 2 366 := by sorry

/-- The final assembly matching exactly the cited `ricciD`. -/
theorem ricciD_decompJ365 : TheoremD 6 6 ∧ TheoremD 5 7 ∧ TheoremD 4 9 ∧ TheoremD 3 15 ∧ TheoremD 2 366 := by
  exact ⟨⟨decompJ365_Z_6_6, decompJ365_W_6_6⟩,
         ⟨decompJ365_Z_5_7, decompJ365_W_5_7⟩,
         ⟨decompJ365_Z_4_9, decompJ365_W_4_9⟩,
         ⟨decompJ365_Z_3_15, decompJ365_W_3_15⟩,
         ⟨decompJ365_Z_2_366, decompJ365_W_2_366⟩⟩

end
end LeanLab.Ricci1937
