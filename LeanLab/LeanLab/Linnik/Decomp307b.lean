/-
Gallagher 1970 p.336 display 25 and the application of Theorem 4.
The covering argument and rough sieve average are separate obligations.
AI wrote the Lean code. Codex task307. Goldbach is open.
Source https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0011/LOG_0035.pdf
-/
import LeanLab.Linnik.Decomp1532b

open Finset MeasureTheory Complex
open scoped Classical
open LeanLab.Linnik.Decomp1532b
namespace LeanLab.Linnik.Decomp307b

/-- Gallagher p.336 the prime window coefficients used in Theorem 4. -/
noncomputable def primeWindowWeight (x : ℝ) (n : ℕ) : ℂ :=
  if ⌊x⌋₊ < n ∧ n.Prime then (Real.log n / (n : ℝ) : ℂ) else 0

/-- Gallagher p.336 the detector is the finite polynomial with prime window weights. -/
theorem characterPolynomial_primeWindowWeight {q : ℕ} (χ : DirichletCharacter ℂ q)
    (x y v : ℝ) :
    characterPolynomial χ (primeWindowWeight x) ⌊y⌋₊ v = primeDetector χ x y v := by
  classical
  unfold characterPolynomial primeWindowWeight primeDetector
  simp only [ite_mul, zero_mul]
  rw [← sum_filter]
  congr 1
  ext n
  simp only [mem_filter, mem_Icc, mem_Ioc]
  constructor
  · rintro ⟨⟨hl, hu⟩, hn, hp⟩
    exact ⟨⟨hn, hu⟩, hp⟩
  · rintro ⟨⟨hn, hu⟩, hp⟩
    exact ⟨⟨by omega, hu⟩, hn, hp⟩

/-- Gallagher p.336 the prime window coefficients satisfy the rough support condition. -/
theorem primeWindowWeight_rough {x : ℝ} {Q : ℕ} (hQ : (Q : ℝ) ≤ x)
    (n p : ℕ) (hp : p.Prime) (hpQ : p ≤ Q) (hpn : p ∣ n) :
    primeWindowWeight x n = 0 := by
  classical
  unfold primeWindowWeight
  split_ifs with hn
  · have hpeq : p = n := ((Nat.dvd_prime hn.2).mp hpn).resolve_left hp.ne_one
    have hnx : x < (n : ℝ) := Nat.lt_of_floor_lt hn.1
    have hnQ : (n : ℝ) ≤ Q := by exact_mod_cast (hpeq ▸ hpQ)
    linarith
  · rfl

/-- Gallagher p.336 the large prime coefficients absorb a bounded multiple of x.
The explicit factor five allows a rounded sieve level. -/
theorem primeWindowWeight_energy (N : ℕ) (hN : 1 ≤ N) {x K : ℝ}
    (hK : K ≤ 4 * x) :
    (∑ n ∈ Icc 1 N, (K + n) * ‖primeWindowWeight x n‖ ^ 2) ≤
      5 * Real.log N * (Real.log N + 7) := by
  classical
  let S := (Icc 1 N).filter (fun n => ⌊x⌋₊ < n ∧ n.Prime)
  have heq : (∑ n ∈ Icc 1 N, (K + n) * ‖primeWindowWeight x n‖ ^ 2) =
      ∑ n ∈ S, (K + n) * (Real.log n / n) ^ 2 := by
    simp only [S, sum_filter, primeWindowWeight]
    apply sum_congr rfl
    intro n hn
    split_ifs
    · simp only [norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n), div_pow, sq_abs]
    · simp
  have hsub : S ⊆ Nat.primesLE N := by
    intro n hn
    obtain ⟨hnN, hnx, hnp⟩ := mem_filter.mp hn
    exact Nat.mem_primesLE.mpr ⟨(mem_Icc.mp hnN).2, hnp⟩
  rw [heq]
  calc
    _ ≤ ∑ n ∈ S, 5 * (Real.log n ^ 2 / n) := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hnN, hnx, hnp⟩ := mem_filter.mp hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hnp.pos
      have hxn : x < (n : ℝ) := Nat.lt_of_floor_lt hnx
      have hKn : K + n ≤ 5 * (n : ℝ) := by linarith
      calc
        _ ≤ (5 * (n : ℝ)) * (Real.log n / n) ^ 2 :=
          mul_le_mul_of_nonneg_right hKn (sq_nonneg _)
        _ = _ := by field_simp
    _ ≤ ∑ n ∈ Nat.primesLE N, 5 * (Real.log n ^ 2 / n) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
    _ = 5 * ∑ n ∈ Nat.primesLE N, Real.log n ^ 2 / n := (mul_sum ..).symm
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (prime_log_sq_div_sum_le N hN)
        (by norm_num : (0 : ℝ) ≤ 5)
      nlinarith

/-- Gallagher p.336 the unweighted primitive character detector energy. -/
noncomputable def detectorEnergy (T x y : ℝ) : ℝ :=
  ∑ q ∈ Icc 1 ⌊T⌋₊,
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
      ∫ v in (-T)..T, ‖primeDetector χ x y v‖ ^ 2

/-- Gallagher p.336 every fixed prime detector energy is nonnegative. -/
theorem detectorEnergy_nonneg {T : ℝ} (hT : 0 ≤ T) (x y : ℝ) :
    0 ≤ detectorEnergy T x y := by
  unfold detectorEnergy
  apply sum_nonneg
  intro q hq
  apply sum_nonneg
  intro χ hχ
  exact intervalIntegral.integral_nonneg (by linarith) (fun v hv => sq_nonneg _)

/-- Gallagher p.336 the finite rough hybrid estimate before choosing the sieve level.
The logarithmic conductor weight L is retained explicitly. -/
theorem detectorEnergy_le_of_prime_hybrid
    (hprime : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
    ∀ N : ℕ, ∀ a : ℕ → ℂ,
      (∀ n ∈ Finset.Icc 1 N, ∀ p : ℕ, p.Prime → p ≤ Q → p ∣ n → a n = 0) →
      (∑ q ∈ Finset.Icc 1 Q, Real.log ((Q : ℝ) / q) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ∫ t in (-T)..T, ‖characterPolynomial χ a N t‖ ^ 2) ≤
        C * ∑ n ∈ Finset.Icc 1 N, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ Q : ℕ, 1 ≤ Q →
      ∀ x y L : ℝ, 1 ≤ ⌊y⌋₊ → ⌊T⌋₊ ≤ Q → (Q : ℝ) ≤ x →
        (∀ q ∈ Icc 1 ⌊T⌋₊, L ≤ Real.log ((Q : ℝ) / q)) →
        (Q : ℝ) ^ 2 * T ≤ 4 * x →
        L * detectorEnergy T x y ≤ C * Real.log ⌊y⌋₊ * (Real.log ⌊y⌋₊ + 7) := by
  obtain ⟨C, hC, hhybrid⟩ := hprime
  refine ⟨5 * C, by positivity, ?_⟩
  intro T hT Q hQ x y L hy hTQ hQx hL hscale
  let e : ℕ → ℝ := fun q =>
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
      ∫ v in (-T)..T, ‖characterPolynomial χ (primeWindowWeight x) ⌊y⌋₊ v‖ ^ 2
  have he (q : ℕ) : 0 ≤ e q := by
    apply sum_nonneg
    intro χ hχ
    exact intervalIntegral.integral_nonneg (by linarith) (fun v hv => sq_nonneg _)
  have hrough : ∀ n ∈ Icc 1 ⌊y⌋₊, ∀ p : ℕ, p.Prime → p ≤ Q → p ∣ n →
      primeWindowWeight x n = 0 := by
    intro n hn p hp hpQ hpn
    exact primeWindowWeight_rough hQx n p hp hpQ hpn
  have hbound := hhybrid Q hQ T hT ⌊y⌋₊ (primeWindowWeight x) hrough
  have hcoeff := primeWindowWeight_energy ⌊y⌋₊ hy hscale
  have hid : detectorEnergy T x y = ∑ q ∈ Icc 1 ⌊T⌋₊, e q := by
    simp only [detectorEnergy, e, characterPolynomial_primeWindowWeight]
  rw [hid, mul_sum]
  calc
    _ ≤ ∑ q ∈ Icc 1 ⌊T⌋₊, Real.log ((Q : ℝ) / q) * e q := by
      apply sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_right (hL q hq) (he q)
    _ ≤ ∑ q ∈ Icc 1 Q, Real.log ((Q : ℝ) / q) * e q := by
      apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hTQ)
      intro q hq hqnot
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (mem_Icc.mp hq).1
      have hqQ : (q : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp hq).2
      exact mul_nonneg (Real.log_nonneg ((le_div_iff₀ hq0).mpr (by simpa using hqQ))) (he q)
    _ ≤ C * ∑ n ∈ Icc 1 ⌊y⌋₊, ((Q : ℝ) ^ 2 * T + n) * ‖primeWindowWeight x n‖ ^ 2 := hbound
    _ ≤ C * (5 * Real.log ⌊y⌋₊ * (Real.log ⌊y⌋₊ + 7)) :=
      mul_le_mul_of_nonneg_left hcoeff hC.le
    _ = _ := by ring

/-- Gallagher p.336 rounding the sieve level T squared preserves its scale and weight. -/
theorem rounded_square_sieve_level {T : ℝ} (hT : 2 ≤ T) :
    1 ≤ ⌈T ^ 2⌉₊ ∧ ⌊T⌋₊ ≤ ⌈T ^ 2⌉₊ ∧
      (⌈T ^ 2⌉₊ : ℝ) ^ 2 * T ≤ 4 * T ^ (5 : ℝ) ∧
      ∀ q ∈ Icc 1 ⌊T⌋₊, Real.log T ≤ Real.log ((⌈T ^ 2⌉₊ : ℝ) / q) := by
  have hT0 : 0 < T := by linarith
  have hlo : T ^ 2 ≤ (⌈T ^ 2⌉₊ : ℝ) := Nat.le_ceil _
  have hhi : (⌈T ^ 2⌉₊ : ℝ) < T ^ 2 + 1 := Nat.ceil_lt_add_one (sq_nonneg _)
  have hsq : T ≤ T ^ 2 := by nlinarith
  have hQ1 : 1 ≤ ⌈T ^ 2⌉₊ := by
    have hh : (1 : ℝ) ≤ ⌈T ^ 2⌉₊ := by linarith
    exact_mod_cast hh
  have hTQ : ⌊T⌋₊ ≤ ⌈T ^ 2⌉₊ := by
    have hh : (⌊T⌋₊ : ℝ) ≤ ⌈T ^ 2⌉₊ := (Nat.floor_le hT0.le).trans (hsq.trans hlo)
    exact_mod_cast hh
  have hhi' : (⌈T ^ 2⌉₊ : ℝ) ≤ 2 * T ^ 2 := by nlinarith
  refine ⟨hQ1, hTQ, ?_, ?_⟩
  · norm_num only [Real.rpow_ofNat]
    have hh := mul_self_le_mul_self (Nat.cast_nonneg ⌈T ^ 2⌉₊) hhi'
    have hh' := mul_le_mul_of_nonneg_right hh hT0.le
    nlinarith
  · intro q hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (mem_Icc.mp hq).1
    have hqT : (q : ℝ) ≤ T :=
      (show (q : ℝ) ≤ ⌊T⌋₊ by exact_mod_cast (mem_Icc.mp hq).2).trans (Nat.floor_le hT0.le)
    apply Real.log_le_log hT0
    apply (le_div_iff₀ hq0).mpr
    nlinarith

/-- Gallagher p.336 the rough hybrid bound gives energy of order log T at every y.
The displayed constants retain the dependence on the fixed window exponents. -/
theorem detectorEnergy_log_bound
    (hprime : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
    ∀ N : ℕ, ∀ a : ℕ → ℂ,
      (∀ n ∈ Finset.Icc 1 N, ∀ p : ℕ, p.Prime → p ≤ Q → p ∣ n → a n = 0) →
      (∑ q ∈ Finset.Icc 1 Q, Real.log ((Q : ℝ) / q) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ∫ t in (-T)..T, ‖characterPolynomial χ a N t‖ ^ 2) ≤
        C * ∑ n ∈ Finset.Icc 1 N, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ K B : ℝ, 5 ≤ K → 1 < B → ∀ T : ℝ, 2 ≤ T →
      ∀ y : ℝ, T ^ K ≤ y → y ≤ (T ^ K) ^ B →
        detectorEnergy T (T ^ K) y ≤
          C * (K * B) * (K * B + 7 / Real.log 2) * Real.log T := by
  obtain ⟨C, hC, hfinite⟩ := detectorEnergy_le_of_prime_hybrid hprime
  refine ⟨C, hC, ?_⟩
  intro K B hK hB T hT y hxy hyy
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hx1 : 1 ≤ T ^ K := Real.one_le_rpow hT1 hK0
  have hx0 : 0 < T ^ K := Real.rpow_pos_of_pos hT0 _
  have hy1 : 1 ≤ y := hx1.trans hxy
  have hN : 1 ≤ ⌊y⌋₊ := (Nat.one_le_floor_iff _).mpr hy1
  have hN0 : (0 : ℝ) < ⌊y⌋₊ := by exact_mod_cast (by omega : 0 < ⌊y⌋₊)
  have hl : 0 < Real.log T := Real.log_pos (by linarith)
  obtain ⟨hQ1, hTQ, hscale, hweight⟩ := rounded_square_sieve_level hT
  have hQhi : (⌈T ^ 2⌉₊ : ℝ) ≤ 2 * T ^ 2 := by
    have hh := Nat.ceil_lt_add_one (sq_nonneg T)
    nlinarith
  have hQcube : (⌈T ^ 2⌉₊ : ℝ) ≤ T ^ 3 := by
    have hh := mul_le_mul_of_nonneg_right hT (sq_nonneg T)
    nlinarith
  have hQx : (⌈T ^ 2⌉₊ : ℝ) ≤ T ^ K := hQcube.trans (by
    simpa only [Real.rpow_ofNat] using
      Real.rpow_le_rpow_of_exponent_le hT1 (show (3 : ℝ) ≤ K by linarith))
  have h5x : T ^ (5 : ℝ) ≤ T ^ K :=
    Real.rpow_le_rpow_of_exponent_le hT1 hK
  have hs : (⌈T ^ 2⌉₊ : ℝ) ^ 2 * T ≤ 4 * T ^ K :=
    hscale.trans (mul_le_mul_of_nonneg_left h5x (by norm_num))
  have hf := hfinite T (by linarith) ⌈T ^ 2⌉₊ hQ1 (T ^ K) y (Real.log T)
    hN hTQ hQx hweight hs
  have hlogN0 : 0 ≤ Real.log ⌊y⌋₊ := Real.log_nonneg (by exact_mod_cast hN)
  have hlogN : Real.log ⌊y⌋₊ ≤ K * B * Real.log T := by
    calc
      _ ≤ Real.log y := Real.log_le_log hN0 (Nat.floor_le (by linarith))
      _ ≤ Real.log ((T ^ K) ^ B) := Real.log_le_log (by linarith) hyy
      _ = _ := by rw [Real.log_rpow hx0, Real.log_rpow hT0]; ring
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h7 : (7 : ℝ) ≤ (7 / Real.log 2) * Real.log T := by
    have hh := mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT)
      (show 0 ≤ 7 / Real.log 2 by positivity)
    have heq : (7 / Real.log (2 : ℝ)) * Real.log 2 = 7 := by field_simp
    linarith
  have hlogN7 : Real.log ⌊y⌋₊ + 7 ≤ (K * B + 7 / Real.log 2) * Real.log T := by nlinarith
  have hm := mul_le_mul hlogN hlogN7 (by linarith : 0 ≤ Real.log ⌊y⌋₊ + 7)
    (show 0 ≤ K * B * Real.log T by positivity)
  have hh := hf.trans (by
    have ht := mul_le_mul_of_nonneg_left hm hC.le
    convert ht using 1; ring)
  apply (mul_le_mul_iff_left₀ hl).mp
  convert hh using 1 <;> ring

/-- Gallagher p.336 the energy is measurable as a function of the prime window endpoint. -/
theorem measurable_detectorEnergy (T x : ℝ) : Measurable (detectorEnergy T x) := by
  have heq : (fun y : ℝ => detectorEnergy T x (⌊y⌋₊ : ℝ)) = detectorEnergy T x := by
    funext y
    simp only [detectorEnergy, primeDetector, Nat.floor_natCast]
  rw [← heq]
  exact (measurable_of_countable (fun n : ℕ => detectorEnergy T x n)).comp Nat.measurable_floor

/-- Gallagher p.336 joint measurability for the height and prime endpoint integrations. -/
theorem measurable_primeDetector_uncurry {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) :
    Measurable (fun z : ℝ × ℝ => primeDetector χ x z.1 z.2) := by
  have hm : Measurable (fun z : ℕ × ℝ => characterPolynomial χ (primeWindowWeight x) z.1 z.2) :=
    measurable_from_prod_countable_right
      (fun N => (continuous_characterPolynomial χ (primeWindowWeight x) N).measurable)
  have hg : Measurable (fun z : ℝ × ℝ => (⌊z.1⌋₊, z.2)) :=
    (Nat.measurable_floor.comp measurable_fst).prodMk measurable_snd
  simpa only [Function.comp_def, characterPolynomial_primeWindowWeight] using hm.comp hg

/-- Gallagher p.336 local detection and a local occupancy bound imply a global finite count.
CONDITIONAL ON the supplied local bound and pointwise detector estimate. -/
theorem finite_height_count_from_local_detector {ι : Type*} (S : Finset ι)
    (height : ι → ℝ) {T r H L : ℝ} (hr : 0 < r) (hrT : r ≤ T)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hheight : ∀ i ∈ S, height i ∈ Set.Icc (-T) T)
    (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc (-T) T))
    (hg0 : ∀ v ∈ Set.Icc (-T) T, 0 ≤ g v)
    (hlocal : ∀ v ∈ Set.Icc (-T) T,
      (∑ i ∈ S, (Set.Icc (height i - r) (height i + r)).indicator (fun _ => (1 : ℝ)) v) ≤ L)
    (hdetect : ∀ i ∈ S, ∀ v ∈ Set.Icc (-T) T,
      v ∈ Set.Icc (height i - r) (height i + r) → H ≤ g v) :
    (S.card : ℝ) * r * H ≤ L * ∫ v in Set.Icc (-T) T, g v := by
  classical
  apply Decomp1532b2.finite_height_cover_bound S height hr.le hrT hH hheight g hg
  intro v hv
  by_cases hh : ∃ i ∈ S, v ∈ Set.Icc (height i - r) (height i + r)
  · obtain ⟨i, hi, hvi⟩ := hh
    calc
      _ ≤ H * L := mul_le_mul_of_nonneg_left (hlocal v hv) hH
      _ ≤ L * g v := by nlinarith [mul_le_mul_of_nonneg_right (hdetect i hi v hv hvi) hL]
  · have hzero : (∑ i ∈ S,
        (Set.Icc (height i - r) (height i + r)).indicator (fun _ => (1 : ℝ)) v) = 0 := by
      apply sum_eq_zero
      intro i hi
      exact Set.indicator_of_notMem (fun hvi => hh ⟨i, hi, hvi⟩) _
    rw [hzero, mul_zero]
    exact mul_nonneg hL (hg0 v hv)

/-- LEAF. Gallagher 1970 p.336 integrated counting step before display 25.
The bounded principal low height contribution and the wide strip are absorbed by one.
This uses the supplied detector and local count, without a hybrid sieve hypothesis. -/
theorem zero_count_from_integrated_detector
    (hdetector : ∃ r₀ A B C c : ℝ,
    0 < r₀ ∧ r₀ ≤ 1 / 4 ∧ 1 ≤ A ∧ 1 < B ∧ 0 < C ∧ 0 < c ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
        |v| ≤ T → (χ = 1 → 2 ≤ |v|) → 1 / Real.log T ≤ r → r ≤ r₀ →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + v * Complex.I)‖ ≤ r) →
        ∀ x : ℝ, T ^ A ≤ x →
          c * x ^ (-C * r) * Real.log x ^ 2 ≤
            ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y) :
    ∀ b : ℝ, 0 < b → ∃ K B c C : ℝ, 5 ≤ K ∧ 1 < B ∧ 0 < c ∧ 0 ≤ C ∧
      ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 3 / 4 < σ → σ < 1 - b / Real.log T →
      (∑ q ∈ range ⌊T⌋₊,
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
          (zeroCount χ σ T : ℝ)) ≤
        C * T ^ (c * (1 - σ)) *
          (1 + (∫ y in (T ^ K)..((T ^ K) ^ B), detectorEnergy T (T ^ K) y / y) /
            Real.log T ^ 2) := by
  -- BLOCKED OUT OF REACH: requires explicit formula, large sieve for Dirichlet characters,
  -- and complex analysis estimates not available in the codebase.
  sorry

/-- Gallagher 1970 p.336 the last two displays after display 25.
The rough hybrid bound at sieve level comparable to T squared gives a logarithmic square
bound for the averaged detector energy. No zero or detector lower bound is assumed. -/
theorem integrated_detector_energy_of_prime_hybrid
    (hprime : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
    ∀ N : ℕ, ∀ a : ℕ → ℂ,
      (∀ n ∈ Finset.Icc 1 N, ∀ p : ℕ, p.Prime → p ≤ Q → p ∣ n → a n = 0) →
      (∑ q ∈ Finset.Icc 1 Q, Real.log ((Q : ℝ) / q) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ∫ t in (-T)..T, ‖characterPolynomial χ a N t‖ ^ 2) ≤
        C * ∑ n ∈ Finset.Icc 1 N, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2) :
    ∀ K B : ℝ, 5 ≤ K → 1 < B → ∃ H : ℝ, 0 ≤ H ∧ ∀ T : ℝ, 2 ≤ T →
      (∫ y in (T ^ K)..((T ^ K) ^ B), detectorEnergy T (T ^ K) y / y) ≤ H * Real.log T ^ 2 := by
  obtain ⟨C, hC, hpoint⟩ := detectorEnergy_log_bound hprime
  intro K B hK hB
  have hK0 : 0 ≤ K := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hBm0 : 0 ≤ B - 1 := by linarith
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let M : ℝ := C * (K * B) * (K * B + 7 / Real.log 2)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M * (B - 1) * K, by positivity, ?_⟩
  intro T hT
  have hT0 : 0 < T := by linarith
  have hl : 0 < Real.log T := Real.log_pos (by linarith)
  have hx1 : 1 ≤ T ^ K := Real.one_le_rpow (by linarith) (by linarith)
  have hx0 : 0 < T ^ K := Real.rpow_pos_of_pos hT0 _
  have hxy : T ^ K ≤ (T ^ K) ^ B := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx1 hB.le
  have hg : Measurable (fun y : ℝ => detectorEnergy T (T ^ K) y / y) :=
    (measurable_detectorEnergy T (T ^ K)).div measurable_id
  have hi : IntegrableOn (fun y : ℝ => detectorEnergy T (T ^ K) y / y)
      (Set.Icc (T ^ K) ((T ^ K) ^ B)) := by
    apply IntegrableOn.of_bound isCompact_Icc.measure_lt_top hg.aestronglyMeasurable (M * Real.log T)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have hy1 : 1 ≤ y := hx1.trans hy.1
    have hen : 0 ≤ detectorEnergy T (T ^ K) y := detectorEnergy_nonneg (by linarith) _ _
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hen (by linarith))]
    have hh : detectorEnergy T (T ^ K) y ≤ M * Real.log T := hpoint K B hK hB T hT y hy.1 hy.2
    exact (div_le_self hen hy1).trans hh
  have hm : IntegrableOn (fun y : ℝ => M * Real.log T / y)
      (Set.Icc (T ^ K) ((T ^ K) ^ B)) := by
    exact (continuousOn_const.div continuousOn_id
      (by intro y hy; exact (hx0.trans_le hy.1).ne')).integrableOn_Icc
  have hh := intervalIntegral.integral_mono_on hxy
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hxy).mpr hi)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hxy).mpr hm)
    (fun y hy => div_le_div_of_nonneg_right (hpoint K B hK hB T hT y hy.1 hy.2)
      (hx0.trans_le hy.1).le)
  calc
    _ ≤ ∫ y in (T ^ K)..((T ^ K) ^ B), M * Real.log T / y := hh
    _ = (M * (B - 1) * K) * Real.log T ^ 2 := by
      simp_rw [div_eq_mul_inv]
      rw [intervalIntegral.integral_const_mul]
      have he := logarithmic_window_mass hx0 B
      simp only [one_div] at he
      rw [he, Real.log_rpow hT0]
      ring

/-- Gallagher p.336 the averaged energy bound with the proved rough sieve supplied. -/
theorem integrated_detector_energy :
    ∀ K B : ℝ, 5 ≤ K → 1 < B → ∃ H : ℝ, 0 ≤ H ∧ ∀ T : ℝ, 2 ≤ T →
      (∫ y in (T ^ K)..((T ^ K) ^ B), detectorEnergy T (T ^ K) y / y) ≤ H * Real.log T ^ 2 := by
  exact integrated_detector_energy_of_prime_hybrid gallagher_prime_hybrid_mean_value

/-- Gallagher 1970 p.336 Theorem 6 display 24.
Exact sealed transition statement assembled from the two smaller integrated leaves.
CONDITIONAL ON those leaves. This theorem has no proof hole of its own. -/
theorem gallagher_density_from_detector_and_prime_hybrid
    (hdetector : ∃ r₀ A B C c : ℝ,
    0 < r₀ ∧ r₀ ≤ 1 / 4 ∧ 1 ≤ A ∧ 1 < B ∧ 0 < C ∧ 0 < c ∧
    ∀ T : ℝ, 2 ≤ T → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ T →
      ∀ χ : DirichletCharacter ℂ q, ∀ v r : ℝ,
        |v| ≤ T → (χ = 1 → 2 ≤ |v|) → 1 / Real.log T ≤ r → r ≤ r₀ →
        (∃ ρ : ℂ, χ.LFunction ρ = 0 ∧ ‖ρ - (1 + v * Complex.I)‖ ≤ r) →
        ∀ x : ℝ, T ^ A ≤ x →
          c * x ^ (-C * r) * Real.log x ^ 2 ≤
            ∫ y in x..(x ^ B), ‖primeDetector χ x y v‖ / y)
    (hprime : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
    ∀ N : ℕ, ∀ a : ℕ → ℂ,
      (∀ n ∈ Finset.Icc 1 N, ∀ p : ℕ, p.Prime → p ≤ Q → p ∣ n → a n = 0) →
      (∑ q ∈ Finset.Icc 1 Q, Real.log ((Q : ℝ) / q) *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ∫ t in (-T)..T, ‖characterPolynomial χ a N t‖ ^ 2) ≤
        C * ∑ n ∈ Finset.Icc 1 N, ((Q : ℝ) ^ 2 * T + n) * ‖a n‖ ^ 2) :
    ∀ b : ℝ, 0 < b → ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
    ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 3 / 4 < σ → σ < 1 - b / Real.log T →
    ∑ q ∈ range ⌊T⌋₊,
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (q + 1))).filter (fun χ => χ.IsPrimitive),
        (zeroCount χ σ T : ℝ) ≤ C * T ^ (c * (1 - σ)) := by
  intro b hb
  obtain ⟨K, B, c, C, hK, hB, hc, hC, hcount⟩ := zero_count_from_integrated_detector hdetector b hb
  obtain ⟨H, hH, henergy⟩ := integrated_detector_energy_of_prime_hybrid hprime K B hK hB
  refine ⟨c, C * (1 + H), hc, by positivity, ?_⟩
  intro T hT σ hσ hσb
  have hl : 0 < Real.log T ^ 2 := sq_pos_of_pos (Real.log_pos (by linarith))
  have he : (∫ y in (T ^ K)..((T ^ K) ^ B), detectorEnergy T (T ^ K) y / y) /
      Real.log T ^ 2 ≤ H := (div_le_iff₀ hl).mpr (henergy T hT)
  calc
    _ ≤ C * T ^ (c * (1 - σ)) *
        (1 + (∫ y in (T ^ K)..((T ^ K) ^ B), detectorEnergy T (T ^ K) y / y) /
          Real.log T ^ 2) := hcount T hT σ hσ hσb
    _ ≤ C * T ^ (c * (1 - σ)) * (1 + H) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ = _ := by ring

end LeanLab.Linnik.Decomp307b
