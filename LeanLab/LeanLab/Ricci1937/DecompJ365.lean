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

/-- LEAF. Pages 75, 88 and 89: the remaining positive lower count for Z.
The upper estimate is decompJ365_zCount_upper. The decreasing step Brun lower sieve remains open. -/
theorem decompJ365_Z_lower_6_6 :
    ∀ m : ℤ, m ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℕ, ∀ ξ : ℕ, ξ₀ ≤ ξ →
      c * ξ / Real.log ξ ^ 2 ≤ zCount 6 6 m ξ := by
  sorry

/-- LEAF. Pages 75, 88 and 89: the remaining positive lower count for Z.
The upper estimate is decompJ365_zCount_upper. The decreasing step Brun lower sieve remains open. -/
theorem decompJ365_Z_lower_5_7 :
    ∀ m : ℤ, m ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℕ, ∀ ξ : ℕ, ξ₀ ≤ ξ →
      c * ξ / Real.log ξ ^ 2 ≤ zCount 5 7 m ξ := by
  sorry

/-- LEAF. Pages 75, 88 and 89: the remaining positive lower count for Z.
The upper estimate is decompJ365_zCount_upper. The decreasing step Brun lower sieve remains open. -/
theorem decompJ365_Z_lower_4_9 :
    ∀ m : ℤ, m ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℕ, ∀ ξ : ℕ, ξ₀ ≤ ξ →
      c * ξ / Real.log ξ ^ 2 ≤ zCount 4 9 m ξ := by
  sorry

/-- LEAF. Pages 75, 88 and 89: the remaining positive lower count for Z.
The upper estimate is decompJ365_zCount_upper. The decreasing step Brun lower sieve remains open. -/
theorem decompJ365_Z_lower_3_15 :
    ∀ m : ℤ, m ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℕ, ∀ ξ : ℕ, ξ₀ ≤ ξ →
      c * ξ / Real.log ξ ^ 2 ≤ zCount 3 15 m ξ := by
  sorry

/-- LEAF. Pages 75, 88 and 90: the remaining positive lower count for Z.
The upper estimate is decompJ365_zCount_upper. The decreasing step Brun lower sieve remains open. -/
theorem decompJ365_Z_lower_2_366 :
    ∀ m : ℤ, m ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℕ, ∀ ξ : ℕ, ξ₀ ≤ ξ →
      c * ξ / Real.log ξ ^ 2 ≤ zCount 2 366 m ξ := by
  sorry

/-- LEAF. Page 89, the Z half of Theorem D for (6, 6). -/
theorem decompJ365_Z_6_6 : TheoremDZ 6 6 := by
  exact decompJ365_Z_of_lower decompJ365_Z_lower_6_6

/-- LEAF. Page 89, the W half of Theorem D for (6, 6). -/
theorem decompJ365_W_6_6 : TheoremDW 6 6 := by sorry

/-- LEAF. Page 89, the Z half of Theorem D for (5, 7). -/
theorem decompJ365_Z_5_7 : TheoremDZ 5 7 := by
  exact decompJ365_Z_of_lower decompJ365_Z_lower_5_7

/-- LEAF. Page 89, the W half of Theorem D for (5, 7). -/
theorem decompJ365_W_5_7 : TheoremDW 5 7 := by sorry

/-- LEAF. Page 89, the Z half of Theorem D for (4, 9). -/
theorem decompJ365_Z_4_9 : TheoremDZ 4 9 := by
  exact decompJ365_Z_of_lower decompJ365_Z_lower_4_9

/-- LEAF. Page 89, the W half of Theorem D for (4, 9). -/
theorem decompJ365_W_4_9 : TheoremDW 4 9 := by sorry

/-- LEAF. Page 89, the Z half of Theorem D for (3, 15). -/
theorem decompJ365_Z_3_15 : TheoremDZ 3 15 := by
  exact decompJ365_Z_of_lower decompJ365_Z_lower_3_15

/-- LEAF. Page 89, the W half of Theorem D for (3, 15). -/
theorem decompJ365_W_3_15 : TheoremDW 3 15 := by sorry

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
