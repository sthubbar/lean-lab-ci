import LeanLab.Ricci1937.TheoremsCD
import LeanLab.Ricci1937.CFactorBounds
import LeanLab.Brun1919.Sieve
import LeanLab.PNTSieve.MertensProduct
import LeanLab.PNTSieve.BrunPure
import LeanLab.Ricci1937.Tau23

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
