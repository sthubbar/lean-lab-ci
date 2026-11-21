/-
AI wrote the Lean code. Goldbach is open.
Task616 U-1690. P0072 p. 63 seeds and Buchstab1938 pp. 381 to 383 transfers.
The transfer leaves retain uniform auxiliary domain hypotheses explicitly.
The extension of the printed range ten to fifteen is OPEN.
-/
import LeanLab.AlmostPrimeSums.Finite616
import LeanLab.AlmostPrimeSums.Kernel616
import LeanLab.AlmostPrimeSums.TogashiUchiyamaScale

import LeanLab.PNTPort.StrongPNT.StrongPNT
open Filter Real Finset
noncomputable section
namespace LeanLab.AlmostPrimeSums.Decomp616
open TogashiUchiyamaScale
attribute [local instance] Classical.propDecidable

/-- The least integer strictly above the paper cutoff N to the power one over u.
A strict prime cutoff at this integer excludes exactly the primes at most the paper cutoff. -/
def cutoff (N : ℕ) (u : ℝ) : ℝ := (⌊(N : ℝ) ^ (1 / u)⌋₊ : ℝ) + 1

/-- The integer cutoff keeps the weak prime endpoint in P0072 exactly. -/
theorem cutoff_prime_iff (N p : ℕ) {u : ℝ} (hu : 0 < u) :
    (p : ℝ) < cutoff N u ↔ (p : ℝ) ^ u ≤ N := by
  have hx : 0 ≤ (N : ℝ) ^ (1 / u) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hf : ((p : ℝ) < (⌊(N : ℝ) ^ (1 / u)⌋₊ : ℝ) + 1) ↔
      p ≤ ⌊(N : ℝ) ^ (1 / u)⌋₊ := by
    exact_mod_cast (Nat.lt_add_one_iff : p < ⌊(N : ℝ) ^ (1 / u)⌋₊ + 1 ↔ _)
  rw [cutoff, hf, Nat.le_floor_iff hx, one_div]
  exact Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg p) (Nat.cast_nonneg N) hu

/-- Increasing the paper exponent decreases the integer prime cutoff. -/
theorem cutoff_antitone {N : ℕ} (hN : 1 ≤ N) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    cutoff N v ≤ cutoff N u := by
  unfold cutoff
  have h : (⌊(N : ℝ) ^ (1 / v)⌋₊ : ℝ) ≤ ⌊(N : ℝ) ^ (1 / u)⌋₊ := by
    exact_mod_cast Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hN) (one_div_le_one_div_of_le hu huv))
  exact add_le_add h le_rfl

/-- The exponent six sieve is exactly the sealed S1set, including its weak endpoint. -/
theorem sifted_six (N : ℕ) :
    Finite616.sifted N (cutoff N 6) = TogashiUchiyamaSection5.S1set N := by
  ext n
  simp only [Finite616.sifted, TogashiUchiyamaSection5.S1set,
    TogashiUchiyamaSection5.Aset, Finset.mem_filter]
  apply and_congr_right
  intro hn
  constructor
  · intro hr p hp hprime hpow
    apply hr p hprime
    exact (cutoff_prime_iff N p (by norm_num : (0 : ℝ) < 6)).mpr
      (by exact_mod_cast hpow)
  · intro hr p hprime hcut
    have hpow : p ^ 6 ≤ N := by
      have h := (cutoff_prime_iff N p (by norm_num : (0 : ℝ) < 6)).mp hcut
      exact_mod_cast h
    have hpN : p ≤ N := (Nat.le_self_pow (by decide : 6 ≠ 0) p).trans hpow
    exact hr p (Finset.mem_range.mpr (by omega)) hprime hpow

/-- Increasing a positive paper exponent enlarges the actual P0072 sifted set. -/
theorem sifted_mono_exponent {N : ℕ} (hN : 1 ≤ N) {u v : ℝ}
    (hu : 0 < u) (huv : u ≤ v) :
    Finite616.sifted N (cutoff N u) ⊆ Finite616.sifted N (cutoff N v) :=
  Finite616.sifted_antitone N (cutoff_antitone hN hu huv)

/-- P0072 p. 63 lower coefficient with an arbitrarily small relative error.
This is a paper statement, not a substitute for a proof of it. -/
def Lower (T u c : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, Even N →
    c * M T N ≤ (Finite616.sifted N (cutoff N u)).card + η * M T N

/-- P0072 p. 63 upper coefficient with an arbitrarily small relative error. -/
def Upper (T u c : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, Even N →
    ((Finite616.sifted N (cutoff N u)).card : ℝ) ≤ (c + η) * M T N

/-- The actual auxiliary quotient mass after removing a prime from a P0072 product.
The prime factor test excludes zero quotients and primes absent from the original product. -/
def childMass (N p : ℕ) : ℝ :=
  (∑ n ∈ (Icc 1 N).filter (fun n => n.Coprime N),
    if p ∈ (n * (N - n)).primeFactors then
      LeanLab.BakerHarmanPintz1997.psi (n * (N - n) / p) (p : ℝ) else 0).re

/-- Every auxiliary quotient mass is nonnegative before any analytic estimate. -/
theorem childMass_nonneg (N p : ℕ) : 0 ≤ childMass N p := by
  unfold childMass
  rw [← Complex.reCLM_apply, map_sum]
  apply Finset.sum_nonneg
  intro n hn
  split_ifs with hp
  · unfold LeanLab.BakerHarmanPintz1997.psi
    split_ifs <;> norm_num
  · norm_num

/-- Primes dividing N remove no products from its coprime P0072 sequence. -/
theorem childMass_eq_zero_of_dvd {N p : ℕ} (hp : p.Prime) (hpN : p ∣ N) :
    childMass N p = 0 := by
  unfold childMass
  have hz : ∀ n ∈ (Icc 1 N).filter (fun n => n.Coprime N),
      p ∉ (n * (N - n)).primeFactors := by
    intro n hn hmem
    obtain ⟨hnI, hc⟩ := mem_filter.mp hn
    have hnN := (mem_Icc.mp hnI).2
    have hd := Nat.dvd_of_mem_primeFactors hmem
    have hpn : p ∣ n := by
      rcases hp.dvd_mul.mp hd with h | h
      · exact h
      · have hsub := Nat.dvd_sub hpN h
        simpa only [Nat.sub_sub_self hnN] using hsub
    have hpgcd := Nat.dvd_gcd hpn hpN
    rw [hc] at hpgcd
    exact hp.ne_one (Nat.dvd_one.mp hpgcd)
  have hs : (∑ n ∈ (Icc 1 N).filter (fun n => n.Coprime N),
      if p ∈ (n * (N - n)).primeFactors then
        LeanLab.BakerHarmanPintz1997.psi (n * (N - n) / p) (p : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [if_neg (hz n hn)]
  rw [hs]
  rfl

/-- A finite prime band containing every prime factor of a P0072 input product. -/
def primeBand (N : ℕ) (w z : ℝ) : Finset ℕ :=
  (range (N ^ 2 + 1)).filter fun p => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z

/-- The exact removed mass is the sum of the actual prime quotient masses.
This is the finite prime sum in Buchstab1938 display 7, before any asymptotic step. -/
theorem removed_eq_sum_child {N : ℕ} (hN : 1 < N) (w z : ℝ) :
    (Finite616.removed N w z).re = ∑ p ∈ primeBand N w z, childMass N p := by
  have hc : Finite616.removed N w z =
      ∑ p ∈ primeBand N w z,
        ∑ n ∈ (Icc 1 N).filter (fun n => n.Coprime N),
          if p ∈ (n * (N - n)).primeFactors then
            LeanLab.BakerHarmanPintz1997.psi (n * (N - n) / p) (p : ℝ) else 0 := by
    unfold Finite616.removed
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    have hset : (primeBand N w z).filter (fun p => p ∈ (n * (N - n)).primeFactors) =
        (n * (N - n)).primeFactors.filter (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < z) := by
      ext p
      simp only [primeBand, mem_filter, mem_range]
      constructor
      · rintro ⟨⟨hpN, hpprime, hband⟩, hpf⟩
        exact ⟨hpf, hband⟩
      · rintro ⟨hpf, hband⟩
        have hnN := (mem_Icc.mp (mem_filter.mp hn).1).2
        have hprod : n * (N - n) ≤ N ^ 2 := by
          simpa only [pow_two] using Nat.mul_le_mul hnN (Nat.sub_le N n)
        have hpProd : p ≤ n * (N - n) :=
          Nat.le_of_dvd (Finite616.product_pos hN hn) (Nat.dvd_of_mem_primeFactors hpf)
        exact ⟨⟨by omega, Nat.prime_of_mem_primeFactors hpf, hband⟩, hpf⟩
    rw [← hset, Finset.sum_filter]
  rw [hc, ← Complex.reCLM_apply, map_sum]
  rfl

/-- The same exact prime sum may discard primes dividing N.
No estimate for the remaining coprime prime band is assumed. -/
theorem removed_eq_sum_coprime {N : ℕ} (hN : 1 < N) (w z : ℝ) :
    (Finite616.removed N w z).re =
      ∑ p ∈ (primeBand N w z).filter (fun p => p.Coprime N), childMass N p := by
  rw [removed_eq_sum_child hN, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hc : p.Coprime N
  · simp only [if_pos hc]
  · have hprime := (Finset.mem_filter.mp hp).2.1
    have hpN : p ∣ N := by
      by_contra hd
      exact hc (hprime.coprime_iff_not_dvd.mpr hd)
    simp only [if_neg hc, childMass_eq_zero_of_dvd hprime hpN]

/-- The actual normalization makes zero a valid lower coefficient. -/
theorem lower_zero (T u : ℝ) (hT : 0 < T) : Lower T u 0 := by
  intro η hη
  filter_upwards [section5_size_inputs hT hη] with N hN he
  have hM : 0 ≤ M T N := by linarith [hN.2]
  simp only [zero_mul]
  positivity

/-- A lower seed remains valid at every larger exponent.
CONDITIONAL ON the supplied lower coefficient. -/
theorem lower_mono_exponent (T u v c : ℝ) (hu : 0 < u) (huv : u ≤ v)
    (hlower : Lower T u c) : Lower T v c := by
  intro η hη
  filter_upwards [hlower η hη, eventually_ge_atTop 1] with N hl hN he
  have hcard : ((Finite616.sifted N (cutoff N u)).card : ℝ) ≤
      (Finite616.sifted N (cutoff N v)).card := by
    exact_mod_cast Finset.card_le_card (sifted_mono_exponent hN hu huv)
  exact (hl he).trans (add_le_add hcard le_rfl)

/-- An upper seed remains valid at every smaller positive exponent.
CONDITIONAL ON the supplied upper coefficient. -/
theorem upper_anti_exponent (T u v c : ℝ) (hu : 0 < u) (huv : u ≤ v)
    (hupper : Upper T v c) : Upper T u c := by
  intro η hη
  filter_upwards [hupper η hη, eventually_ge_atTop 1] with N huN hN he
  have hcard : ((Finite616.sifted N (cutoff N u)).card : ℝ) ≤
      (Finite616.sifted N (cutoff N v)).card := by
    exact_mod_cast Finset.card_le_card (sifted_mono_exponent hN hu huv)
  exact hcard.trans (huN he)

/-- A valid coefficient at exponent six gives the exact sealed target.
CONDITIONAL ON the stated coefficient input. No analytic transfer is hidden here. -/
theorem main_term_of_lower (T ε c : ℝ) (hT : 0 < T) (hε : 0 < ε)
    (hc : 26.4612 ≤ c) (hlower : Lower T 6 c) :
    ∀ᶠ N : ℕ in atTop, Even N →
      26.4612 * M T N ≤ (TogashiUchiyamaSection5.S1set N).card + ε * M T N / 2 := by
  have h := hlower (ε / 2) (by positivity)
  filter_upwards [h, section5_size_inputs hT hε] with N hN hs he
  have hM : 0 ≤ M T N := by linarith [hs.2]
  have hbound := hN he
  rw [sifted_six] at hbound
  have hcoeff := mul_le_mul_of_nonneg_right hc hM
  linarith

/-- Buchstab Theorem 1 assembly for the actual P0072 count.
CONDITIONAL ON the lower endpoint bound and the stated upper removed mass estimate. -/
theorem lower_of_removed (T α β c I : ℝ) (hα : 0 < α) (hαβ : α ≤ β)
    (hlower : Lower T β c)
    (hmass : ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, Even N →
      (Finite616.removed N (cutoff N β) (cutoff N α)).re ≤ (2 * I + η) * M T N) :
    Lower T α (c - 2 * I) := by
  intro η hη
  filter_upwards [hlower (η / 2) (by positivity), hmass (η / 2) (by positivity),
    eventually_ge_atTop 2] with N hl hm hN he
  have hwz := cutoff_antitone (by omega : 1 ≤ N) hα hαβ
  have hid := congrArg Complex.re (Finite616.buchstab_count (by omega : 1 < N) hwz)
  simp only [Complex.natCast_re, Complex.sub_re] at hid
  have hl' := hl he
  have hm' := hm he
  nlinarith

/-- Buchstab Theorem 2 assembly for the actual P0072 count.
CONDITIONAL ON the upper endpoint bound and the stated lower removed mass estimate. -/
theorem upper_of_removed (T α β c I : ℝ) (hα : 0 < α) (hαβ : α ≤ β)
    (hupper : Upper T β c)
    (hmass : ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, Even N →
      (2 * I - η) * M T N ≤ (Finite616.removed N (cutoff N β) (cutoff N α)).re) :
    Upper T α (c - 2 * I) := by
  intro η hη
  filter_upwards [hupper (η / 2) (by positivity), hmass (η / 2) (by positivity),
    eventually_ge_atTop 2] with N hu hm hN he
  have hwz := cutoff_antitone (by omega : 1 ≤ N) hα hαβ
  have hid := congrArg Complex.re (Finite616.buchstab_count (by omega : 1 < N) hwz)
  simp only [Complex.natCast_re, Complex.sub_re] at hid
  have hu' := hu he
  have hm' := hm he
  nlinarith

/-- The zero auxiliary minorant is valid on every prime band for positive T.
This is a nonvacuous elementary instance of the lower transfer hypothesis. -/
theorem zero_auxiliary_lower (T α β : ℝ) (hT : 0 < T) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      ∀ p : ℕ, p.Prime → p.Coprime N → cutoff N β ≤ (p : ℝ) → (p : ℝ) < cutoff N α →
      2 * ((0 : ℝ) - δ) * M T N * (log N) ^ 2 /
        ((p : ℝ) * (log ((N : ℝ) / p)) ^ 2) ≤ childMass N p := by
  intro δ hδ
  filter_upwards [section5_size_inputs hT hδ] with N hs he
  intro p hp hpN hge hlt
  have hM : 0 ≤ M T N := by linarith [hs.2]
  have hleft : 2 * ((0 : ℝ) - δ) * M T N * (log N) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) hM) (sq_nonneg _)
  exact (div_nonpos_of_nonpos_of_nonneg hleft
    (mul_nonneg (Nat.cast_nonneg p) (sq_nonneg _))).trans (childMass_nonneg N p)

/-- Both removed mass conclusions hold at equal exponent endpoints with no cited input. -/
theorem equal_removed_bounds (T u η : ℝ) (hT : 0 < T) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, Even N →
      -η * M T N ≤ (Finite616.removed N (cutoff N u) (cutoff N u)).re ∧
      (Finite616.removed N (cutoff N u) (cutoff N u)).re ≤ η * M T N := by
  filter_upwards [section5_size_inputs hT hη, eventually_ge_atTop 2] with N hs hN he
  have hM : 0 ≤ M T N := by linarith [hs.2]
  have hz : Finite616.removed N (cutoff N u) (cutoff N u) = 0 := by
    rw [Finite616.removed_eq (by omega : 1 < N) le_rfl]
    exact sub_self _
  rw [hz]
  simp only [Complex.zero_re]
  constructor <;> nlinarith

/-! ## Pass 2 (2026-11-18): the prime-sum / integral transfer

With `L = log N`, `A = cutoff N β`, `B = cutoff N α`, `φ t = log (N / t) / log t`,
`ṽ t = 1 / (t log t log²(N / t))` and `K z = log z - 1/z` (so `K' = kernel`), we have

* the change of variables `z = φ t`:  `L² * ∫_A^B U (φ t) * ṽ t dt = ∫_{φ B}^{φ A} U z * kernel z`,
* Abel summation over the Chebyshev increments `θ n - θ (n-1) = log n · [n prime]`, which
  identifies the prime sum with that integral up to an error `O(ε_N Σ)` where
  `ε_N = sup_{t ≥ N^(1/16)} |θ t / t - 1| → 0` by the lab's explicit PNT.
-/

/-- The P0072 cutoff is one more than a natural number. -/
private theorem cutoff_eq_coe_succ (N : ℕ) (u : ℝ) :
    cutoff N u = ((⌊(N : ℝ) ^ (1 / u)⌋₊ + 1 : ℕ) : ℝ) := by
  unfold cutoff
  push_cast
  ring

/-- Members of the prime band lie in the integer interval bounded by the two cutoffs. -/
private theorem primeBand_subset_Ico_filter {N : ℕ} {β α : ℝ} (hβ : 0 < β) (hα : 0 < α) :
    primeBand N (cutoff N β) (cutoff N α) ⊆
      (Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊ + 1)).filter Nat.Prime := by
  intro p hp
  simp only [primeBand, mem_filter] at hp
  obtain ⟨-, hprime, hw, hz⟩ := hp
  refine mem_filter.mpr ⟨mem_Ico.mpr ⟨?_, ?_⟩, hprime⟩
  · rw [cutoff_eq_coe_succ] at hw
    exact_mod_cast hw
  · rw [cutoff_eq_coe_succ] at hz
    exact_mod_cast hz

/-- The Chebyshev theta increments are exactly the logarithms of primes. -/
private theorem theta_sub_theta_pred (n : ℕ) :
    Chebyshev.theta (n : ℝ) - Chebyshev.theta (((n - 1 : ℕ)) : ℝ) =
      if n.Prime then Real.log (n : ℝ) else 0 := by
  match n with
  | 0 => simp
  | k + 1 =>
    by_cases hk : (k + 1).Prime
    · rw [Nat.add_sub_cancel, if_pos hk, Chebyshev.theta_eq_sum_primesLE_log,
        Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_succ, if_pos hk,
        Finset.sum_insert (Nat.notMem_primesLE k)]
      ring
    · rw [Nat.add_sub_cancel, if_neg hk, Chebyshev.theta_eq_sum_primesLE_log,
        Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_succ, if_neg hk]
      ring

/-- The Chebyshev theta function is the sum of its own increments. -/
private theorem sum_range_theta_diff (n : ℕ) :
    ∑ i ∈ Finset.range n,
        (Chebyshev.theta (i : ℝ) - Chebyshev.theta (((i - 1 : ℕ)) : ℝ)) =
      Chebyshev.theta (((n - 1 : ℕ)) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.add_sub_cancel]
    ring

/-- `Real.exp (-c * s)` written with the product inside the negation. -/
private theorem exp_neg_mul_eq (c s : ℝ) : Real.exp (-c * s) = Real.exp (-(c * s)) := by
  rw [neg_mul]

set_option maxHeartbeats 1000000 in
/-- Explicit PNT error in Chebyshev `θ` form, with the rate of the lab's `StrongPNT`. -/
private theorem theta_abs_error_eventually :
    ∃ c > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      |Chebyshev.theta x - x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) + 2 * Real.sqrt x * Real.log x := by
  obtain ⟨c, hc, hO⟩ := StrongPNT
  obtain ⟨C₀, hC₀⟩ := hO.bound
  refine ⟨c, hc, max C₀ 0, le_max_right _ _, ?_⟩
  filter_upwards [hC₀, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  simp only [Pi.sub_apply, id_eq] at hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1' : (1 : ℝ) ≤ x := le_of_lt hx1
  have hnorm : ‖x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 2))‖ =
      x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 2)) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hnorm] at hx
  have hA : (0 : ℝ) ≤ x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 2)) := by positivity
  have hpsi : ‖Chebyshev.psi x - x‖ ≤
      max C₀ 0 * (x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 2))) :=
    hx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hA)
  have hsqrt : Real.log x ^ ((1 : ℝ) / 2) = Real.sqrt (Real.log x) := (Real.sqrt_eq_rpow _).symm
  rw [hsqrt] at hpsi
  have hsplit : Chebyshev.theta x - x =
      -(Chebyshev.psi x - Chebyshev.theta x) + (Chebyshev.psi x - x) := by ring
  have h1 := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx1'
  have h2 : ‖Chebyshev.psi x - x‖ = |Chebyshev.psi x - x| := rfl
  rw [h2] at hpsi
  rw [hsplit]
  calc |-(Chebyshev.psi x - Chebyshev.theta x) + (Chebyshev.psi x - x)|
      ≤ |-(Chebyshev.psi x - Chebyshev.theta x)| + |Chebyshev.psi x - x| := abs_add_le _ _
    _ = |Chebyshev.psi x - Chebyshev.theta x| + |Chebyshev.psi x - x| := by rw [abs_neg]
    _ ≤ 2 * Real.sqrt x * Real.log x
        + max C₀ 0 * (x * Real.exp (-c * Real.sqrt (Real.log x))) := add_le_add h1 hpsi
    _ = max C₀ 0 * x * Real.exp (-c * Real.sqrt (Real.log x))
        + 2 * Real.sqrt x * Real.log x := by ring

/-- `|θ t - t| ≤ ε t` uniformly on the whole range `t ≥ N^(1/16)`, for `N` large. -/
private theorem theta_uniform_error {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, (N : ℝ) ^ ((1 : ℝ) / 16) ≤ t →
      |Chebyshev.theta t - t| ≤ ε * t := by
  obtain ⟨c, hc, C, hC0, hC⟩ := theta_abs_error_eventually
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hC
  have hroot : Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 16)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hexp0 : Tendsto (fun N : ℕ => Real.exp (-c * Real.sqrt (Real.log (N : ℝ) / 16)))
      atTop (nhds 0) := by
    have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hdiv : Tendsto (fun N : ℕ => Real.log (N : ℝ) / 16) atTop atTop :=
      hlog.atTop_div_const (by norm_num)
    have hsq : Tendsto (fun N : ℕ => Real.sqrt (Real.log (N : ℝ) / 16)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp hdiv
    have hmul : Tendsto (fun N : ℕ => c * Real.sqrt (Real.log (N : ℝ) / 16)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hc hsq
    have hneg : Tendsto (fun N : ℕ => -(c * Real.sqrt (Real.log (N : ℝ) / 16))) atTop atBot :=
      tendsto_neg_atTop_atBot.comp hmul
    have hexp := Real.tendsto_exp_atBot.comp hneg
    simpa only [exp_neg_mul_eq, Function.comp_def] using hexp
  have hexpC : Tendsto (fun N : ℕ => C * Real.exp (-c * Real.sqrt (Real.log (N : ℝ) / 16)))
      atTop (nhds 0) := by
    simpa using hexp0.const_mul C
  have hpow0 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 64 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (y := 1 / 64) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hpowC : Tendsto (fun N : ℕ => (8 : ℝ) * (N : ℝ) ^ (-(1 / 64 : ℝ))) atTop (nhds 0) := by
    simpa using hpow0.const_mul 8
  filter_upwards [hroot.eventually (eventually_ge_atTop (max T 4)),
    hexpC.eventually (eventually_le_nhds (by linarith : (0 : ℝ) < ε / 2)),
    hpowC.eventually (eventually_le_nhds (by linarith : (0 : ℝ) < ε / 2)),
    eventually_ge_atTop 2] with N hN hCe hPe hN2
  intro t ht
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hrootN : (4 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 16) := le_trans (le_max_right _ _) hN
  have hTle : T ≤ (N : ℝ) ^ ((1 : ℝ) / 16) := le_trans (le_max_left _ _) hN
  have ht4 : (4 : ℝ) ≤ t := hrootN.trans ht
  have htT : T ≤ t := hTle.trans ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hlogN : Real.log ((N : ℝ) ^ ((1 : ℝ) / 16)) = Real.log (N : ℝ) / 16 := by
    rw [Real.log_rpow hNpos]
    ring
  have hlog_le : Real.log (N : ℝ) / 16 ≤ Real.log t := by
    rw [← hlogN]
    exact Real.log_le_log (by positivity) ht
  have hCee : C * Real.exp (-c * Real.sqrt (Real.log t)) ≤ ε / 2 := by
    have hle : Real.exp (-c * Real.sqrt (Real.log t)) ≤
        Real.exp (-c * Real.sqrt (Real.log (N : ℝ) / 16)) := by
      apply Real.exp_le_exp.mpr
      have hs : Real.sqrt (Real.log (N : ℝ) / 16) ≤ Real.sqrt (Real.log t) :=
        Real.sqrt_le_sqrt hlog_le
      nlinarith
    calc C * Real.exp (-c * Real.sqrt (Real.log t))
        ≤ C * Real.exp (-c * Real.sqrt (Real.log (N : ℝ) / 16)) :=
          mul_le_mul_of_nonneg_left hle hC0
      _ ≤ ε / 2 := hCe
  have hmain : |Chebyshev.theta t - t| ≤
      C * t * Real.exp (-c * Real.sqrt (Real.log t)) + 2 * Real.sqrt t * Real.log t := hT t htT
  have h1 : C * t * Real.exp (-c * Real.sqrt (Real.log t)) ≤ t * (ε / 2) := by
    have heq : C * t * Real.exp (-c * Real.sqrt (Real.log t)) =
        t * (C * Real.exp (-c * Real.sqrt (Real.log t))) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hCee ht0.le
  have hlog4 : Real.log t ≤ 4 * t ^ ((1 : ℝ) / 4) := by
    have h := Real.log_le_rpow_div ht0.le (show (0 : ℝ) < 1 / 4 by norm_num)
    rw [show t ^ ((1 : ℝ) / 4) / (1 / 4) = 4 * t ^ ((1 : ℝ) / 4) by ring] at h
    exact h
  have h2 : 2 * Real.sqrt t * Real.log t ≤ 8 * t ^ ((3 : ℝ) / 4) := by
    have hpos2 : (0 : ℝ) < t ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos ht0 _
    have hpos4 : (0 : ℝ) < t ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos ht0 _
    have hstep : 2 * Real.sqrt t * Real.log t ≤
        2 * t ^ ((1 : ℝ) / 2) * (4 * t ^ ((1 : ℝ) / 4)) := by
      rw [Real.sqrt_eq_rpow]
      nlinarith [hlog4, hpos2]
    have hcomb : 2 * t ^ ((1 : ℝ) / 2) * (4 * t ^ ((1 : ℝ) / 4)) =
        8 * t ^ ((3 : ℝ) / 4) := by
      have hsum : t ^ ((1 : ℝ) / 2) * t ^ ((1 : ℝ) / 4) = t ^ ((3 : ℝ) / 4) := by
        rw [← Real.rpow_add ht0]
        norm_num
      rw [← hsum]
      ring
    exact hstep.trans (le_of_eq hcomb)
  have hkey : (8 : ℝ) ≤ (ε / 2) * t ^ ((1 : ℝ) / 4) := by
    have hN60 : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 64) := Real.rpow_pos_of_pos hNpos _
    have hbase : (8 : ℝ) ≤ (ε / 2) * (N : ℝ) ^ ((1 : ℝ) / 64) := by
      have hmul : (N : ℝ) ^ (-(1 / 64 : ℝ)) * (N : ℝ) ^ ((1 : ℝ) / 64) = 1 := by
        rw [← Real.rpow_add hNpos]
        norm_num
      have hstep := mul_le_mul_of_nonneg_right hPe (le_of_lt hN60)
      calc (8 : ℝ) = 8 * ((N : ℝ) ^ (-(1 / 64 : ℝ)) * (N : ℝ) ^ ((1 : ℝ) / 64)) := by
            rw [hmul]; ring
        _ = (8 * (N : ℝ) ^ (-(1 / 64 : ℝ))) * (N : ℝ) ^ ((1 : ℝ) / 64) := by ring
        _ ≤ (ε / 2) * (N : ℝ) ^ ((1 : ℝ) / 64) := hstep
    have hmono : (N : ℝ) ^ ((1 : ℝ) / 64) ≤ t ^ ((1 : ℝ) / 4) := by
      have h1 : ((N : ℝ) ^ ((1 : ℝ) / 16)) ^ ((1 : ℝ) / 4) ≤ t ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos hNpos _)) ht (by norm_num)
      rw [← Real.rpow_mul (le_of_lt hNpos),
        show (1 : ℝ) / 16 * ((1 : ℝ) / 4) = 1 / 64 by norm_num] at h1
      exact h1
    calc (8 : ℝ) ≤ (ε / 2) * (N : ℝ) ^ ((1 : ℝ) / 64) := hbase
      _ ≤ (ε / 2) * t ^ ((1 : ℝ) / 4) := mul_le_mul_of_nonneg_left hmono (by linarith)
  have h3 : 8 * t ^ ((3 : ℝ) / 4) ≤ (ε / 2) * t := by
    have hsplit : t ^ ((1 : ℝ) / 4) * t ^ ((3 : ℝ) / 4) = t := by
      rw [← Real.rpow_add ht0]
      norm_num
    have hpos34 : (0 : ℝ) < t ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos ht0 _
    calc 8 * t ^ ((3 : ℝ) / 4) = (8 : ℝ) * t ^ ((3 : ℝ) / 4) := rfl
      _ ≤ ((ε / 2) * t ^ ((1 : ℝ) / 4)) * t ^ ((3 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_right hkey (le_of_lt hpos34)
      _ = (ε / 2) * t := by rw [mul_assoc, hsplit]
  nlinarith [hmain, h1, h2, h3]

/-! ### Batch 2: Abel summation against the θ increments, and Riemann/integral comparisons -/

/-- `(n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ)` for positive naturals. -/
private theorem nat_cast_pred (n : ℕ) (hn : 1 ≤ n) : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
  push_cast [Nat.cast_sub hn]
  ring

/-- Sums of consecutive differences of a sequence vanishing at zero telescope. -/
private theorem sum_range_diff (H : ℕ → ℝ) (h0 : H 0 = 0) (n : ℕ) :
    ∑ i ∈ Finset.range n, (H i - H (i - 1)) = H (n - 1) := by
  rcases n with _ | n
  · simpa using h0.symm
  · rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_cancel, Nat.reduceSub, sub_self, add_zero]
    rw [Finset.sum_range_sub, h0]
    ring

/-- The index-weighted telescope `Σ i (g i - g (i+1)) ≤ k g k + Σ g`. -/
private theorem sum_Ico_idx_mul_sub_le {k m : ℕ} (hkm : k < m) {G : ℝ → ℝ}
    (hnn : ∀ t ∈ Set.Icc (k : ℝ) (m : ℝ), 0 ≤ G t) :
    ∑ i ∈ Finset.Ico k (m - 1), (i : ℝ) * (G (i : ℝ) - G ((i + 1 : ℕ) : ℝ))
      ≤ (k : ℝ) * G (k : ℝ) + ∑ i ∈ Finset.Ico k m, G (i : ℝ) := by
  have hsplit : ∀ i : ℕ, (i : ℝ) * (G (i : ℝ) - G ((i + 1 : ℕ) : ℝ)) =
      ((i : ℝ) * G (i : ℝ) - ((i + 1 : ℕ) : ℝ) * G ((i + 1 : ℕ) : ℝ))
        + G ((i + 1 : ℕ) : ℝ) := by
    intro i
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib]
  have htel : ∑ i ∈ Finset.Ico k (m - 1),
      ((i : ℝ) * G (i : ℝ) - ((i + 1 : ℕ) : ℝ) * G ((i + 1 : ℕ) : ℝ))
      = (k : ℝ) * G (k : ℝ) - ((m - 1 : ℕ) : ℝ) * G (((m - 1 : ℕ)) : ℝ) := by
    have h := Finset.sum_Ico_sub (f := fun j : ℕ => (j : ℝ) * G ((j : ℝ)))
      (m := k) (n := m - 1) (by omega)
    have hneg : ∑ i ∈ Finset.Ico k (m - 1),
        ((i : ℝ) * G (i : ℝ) - ((i + 1 : ℕ) : ℝ) * G ((i + 1 : ℕ) : ℝ))
        = -∑ i ∈ Finset.Ico k (m - 1),
          ((((i + 1 : ℕ)) : ℝ) * G (((i + 1 : ℕ)) : ℝ) - (i : ℝ) * G (i : ℝ)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hneg, h]
    ring
  rw [htel]
  -- the shifted sum is dominated by the full one
  have hm1k : (k : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : k ≤ m - 1)
  have hm1m : ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : m - 1 ≤ m)
  have hgb : (0 : ℝ) ≤ G (((m - 1 : ℕ)) : ℝ) := hnn _ ⟨hm1k, hm1m⟩
  have hshift' : ∑ i ∈ Finset.Ico k (m - 1), G ((i + 1 : ℕ) : ℝ) ≤
      ∑ i ∈ Finset.Ico k m, G (i : ℝ) := by
    have hadd := Finset.sum_Ico_add' (fun j : ℕ => G ((j : ℝ))) k (m - 1) 1
    rw [show m - 1 + 1 = m by omega] at hadd
    rw [hadd]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [Finset.mem_Ico] at hi ⊢
      omega
    · intro i hi _
      simp only [Finset.mem_Ico] at hi
      have hk' : (k : ℝ) ≤ (i : ℝ) := by exact_mod_cast (by omega : k ≤ i)
      have hb' : (i : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : i ≤ m)
      exact hnn _ ⟨hk', hb'⟩
  have hg0 : (0 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) * G (((m - 1 : ℕ)) : ℝ) :=
    mul_nonneg (by positivity) hgb
  linarith [hshift', hg0]

/-- Summation by parts against the Chebyshev increment measure. -/
private theorem abs_sum_theta_increment_sub_le {k m : ℕ} {G : ℝ → ℝ} {ε : ℝ}
    (hk : 2 ≤ k) (hlt : k < m) (hε0 : 0 ≤ ε)
    (hGanti : AntitoneOn G (Set.Icc ((k : ℝ) - 1) (m : ℝ)))
    (hGnn : ∀ t ∈ Set.Icc (k : ℝ) (m : ℝ), 0 ≤ G t)
    (hθ : ∀ t : ℝ, (k : ℝ) - 1 ≤ t → |Chebyshev.theta t - t| ≤ ε * t) :
    |(∑ i ∈ Finset.Ico k m,
        (Chebyshev.theta (i : ℝ) - Chebyshev.theta (((i - 1 : ℕ)) : ℝ)) * G (i : ℝ))
      - ∑ i ∈ Finset.Ico k m, G (i : ℝ)|
      ≤ ε * (4 * (((k : ℝ) * G (k : ℝ)) + ((m : ℝ) * G (((m - 1 : ℕ)) : ℝ))
        + ∑ i ∈ Finset.Ico k m, G (i : ℝ))) := by
  classical
  set H : ℕ → ℝ := fun i => Chebyshev.theta (i : ℝ) - (i : ℝ) with hHdef
  have hH0 : H 0 = 0 := by simp [hHdef]
  have hdiff : ∀ i : ℕ, 1 ≤ i →
      (Chebyshev.theta (i : ℝ) - Chebyshev.theta (((i - 1 : ℕ)) : ℝ)) - 1 = H i - H (i - 1) := by
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [hHdef, Nat.add_sub_cancel]
    push_cast
    ring
  have hkey : (∑ i ∈ Finset.Ico k m,
        (Chebyshev.theta (i : ℝ) - Chebyshev.theta (((i - 1 : ℕ)) : ℝ)) * G (i : ℝ))
      - ∑ i ∈ Finset.Ico k m, G (i : ℝ)
      = ∑ i ∈ Finset.Ico k m, G (i : ℝ) * (H i - H (i - 1)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hi1 : 1 ≤ i := by
      simp only [Finset.mem_Ico] at hi
      omega
    rw [← hdiff i hi1]
    ring
  rw [hkey]
  -- nonnegativity and index facts
  have hkmR : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_of_lt hlt
  have hkmR' : (k : ℝ) < (m : ℝ) := by exact_mod_cast hlt
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hkm1 : (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ m)
  have hgb : (0 : ℝ) ≤ G (((m - 1 : ℕ)) : ℝ) := by
    have h1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := nat_cast_pred m (by omega)
    refine hGnn _ ⟨?_, ?_⟩
    · rw [h1]; linarith
    · rw [h1]; linarith
  have hgk : (0 : ℝ) ≤ G (k : ℝ) := hGnn _ ⟨le_rfl, hkmR⟩
  have hsum0 : (0 : ℝ) ≤ ∑ i ∈ Finset.Ico k m, G (i : ℝ) :=
    Finset.sum_nonneg (fun i hi => by
      simp only [Finset.mem_Ico] at hi
      refine hGnn _ ⟨?_, ?_⟩
      · have h1 : (k : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi.1
        linarith
      · exact_mod_cast (by omega : i ≤ m))
  -- Abel summation by parts
  have hparts := Finset.sum_Ico_by_parts (f := fun i : ℕ => G (i : ℝ))
    (g := fun i : ℕ => H i - H (i - 1)) (m := k) (n := m) hlt
  have hsumH : ∀ n : ℕ, ∑ i ∈ Finset.range n, (H i - H (i - 1)) = H (n - 1) :=
    fun n => sum_range_diff H hH0 n
  simp only [hsumH, smul_eq_mul] at hparts
  rw [hparts]
  -- the three boundary/error estimates
  have hA : |G (((m - 1 : ℕ)) : ℝ) * H (m - 1)| ≤
      ε * ((m : ℝ) * G (((m - 1 : ℕ)) : ℝ)) := by
    have hmm : |H (m - 1)| ≤ ε * (((m - 1 : ℕ)) : ℝ) := by
      have h := hθ (((m - 1 : ℕ)) : ℝ) (by
        have h1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := nat_cast_pred m (by omega)
        linarith)
      simpa only [hHdef] using h
    rw [abs_mul, abs_of_nonneg hgb]
    have hle : ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
      have h1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := nat_cast_pred m (by omega)
      linarith
    have hst1 := mul_le_mul_of_nonneg_left hmm hgb
    have hst2 : G (((m - 1 : ℕ)) : ℝ) * (ε * (((m - 1 : ℕ)) : ℝ))
        ≤ G (((m - 1 : ℕ)) : ℝ) * (ε * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hε0) hgb
    have hst3 : G (((m - 1 : ℕ)) : ℝ) * (ε * (m : ℝ))
        = ε * ((m : ℝ) * G (((m - 1 : ℕ)) : ℝ)) := by ring
    linarith [hst1, hst2, hst3]
  have hB : |G (k : ℝ) * H (k - 1)| ≤ ε * ((k : ℝ) * G (k : ℝ)) := by
    have hcr : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := nat_cast_pred k (by omega)
    have hkk : |H (k - 1)| ≤ ε * (((k - 1 : ℕ)) : ℝ) := by
      have h := hθ (((k - 1 : ℕ)) : ℝ) (by rw [hcr])
      simpa only [hHdef] using h
    rw [abs_mul, abs_of_nonneg hgk]
    have hle : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by rw [hcr]; linarith
    have hst1 := mul_le_mul_of_nonneg_left hkk hgk
    have hst2 : G (k : ℝ) * (ε * (((k - 1 : ℕ)) : ℝ)) ≤ G (k : ℝ) * (ε * (k : ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hε0) hgk
    have hst3 : G (k : ℝ) * (ε * (k : ℝ)) = ε * ((k : ℝ) * G (k : ℝ)) := by ring
    linarith [hst1, hst2, hst3]
  have hC : |∑ i ∈ Finset.Ico k (m - 1), (G ((i + 1 : ℕ) : ℝ) - G (i : ℝ)) * H i| ≤
      ε * ∑ i ∈ Finset.Ico k (m - 1), (i : ℝ) * (G (i : ℝ) - G ((i + 1 : ℕ) : ℝ)) := by
    have hterm : ∀ i ∈ Finset.Ico k (m - 1),
        |(G ((i + 1 : ℕ) : ℝ) - G (i : ℝ)) * H i|
          ≤ ε * ((i : ℝ) * (G (i : ℝ) - G ((i + 1 : ℕ) : ℝ))) := by
      intro i hi
      simp only [Finset.mem_Ico] at hi
      have hki : (k : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi.1
      have hik : ((k : ℝ) - 1) ≤ (i : ℝ) := by linarith
      have him : (i : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : i ≤ m)
      have hsi : ((i + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : i + 1 ≤ m)
      have hik' : ((k : ℝ) - 1) ≤ ((i + 1 : ℕ) : ℝ) := by push_cast; linarith
      have hnn_i : (0 : ℝ) ≤ G (i : ℝ) := hGnn _ ⟨hki, him⟩
      have hle : G ((i + 1 : ℕ) : ℝ) ≤ G (i : ℝ) :=
        hGanti ⟨hik, him⟩ ⟨hik', hsi⟩ (by push_cast; linarith)
      have hidx : |H i| ≤ ε * (i : ℝ) := by
        have h := hθ (i : ℝ) hik
        simpa only [hHdef] using h
      have hprod : (0 : ℝ) ≤ G (i : ℝ) - G ((i + 1 : ℕ) : ℝ) := by linarith
      calc |(G ((i + 1 : ℕ) : ℝ) - G (i : ℝ)) * H i|
          = (G (i : ℝ) - G ((i + 1 : ℕ) : ℝ)) * |H i| := by
            rw [abs_mul, abs_of_nonpos (by linarith)]
            ring
        _ ≤ (G (i : ℝ) - G ((i + 1 : ℕ) : ℝ)) * (ε * (i : ℝ)) :=
            mul_le_mul_of_nonneg_left hidx hprod
        _ = ε * ((i : ℝ) * (G (i : ℝ) - G ((i + 1 : ℕ) : ℝ))) := by ring
    calc |∑ i ∈ Finset.Ico k (m - 1), (G ((i + 1 : ℕ) : ℝ) - G (i : ℝ)) * H i|
        ≤ ∑ i ∈ Finset.Ico k (m - 1), |(G ((i + 1 : ℕ) : ℝ) - G (i : ℝ)) * H i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Ico k (m - 1), ε * ((i : ℝ) * (G (i : ℝ) - G ((i + 1 : ℕ) : ℝ))) :=
          Finset.sum_le_sum hterm
      _ = ε * ∑ i ∈ Finset.Ico k (m - 1), (i : ℝ) * (G (i : ℝ) - G ((i + 1 : ℕ) : ℝ)) := by
          rw [Finset.mul_sum]
  have hT := sum_Ico_idx_mul_sub_le (k := k) (m := m) hlt (G := G)
    (hnn := fun t ht => hGnn t ⟨by linarith [ht.1], ht.2⟩)
  -- triangle inequality
  have htri : |G (((m - 1 : ℕ)) : ℝ) * H (m - 1) - G (k : ℝ) * H (k - 1)
      - ∑ i ∈ Finset.Ico k (m - 1), (G ((i + 1 : ℕ) : ℝ) - G (i : ℝ)) * H i|
      ≤ |G (((m - 1 : ℕ)) : ℝ) * H (m - 1)| + |G (k : ℝ) * H (k - 1)|
        + |∑ i ∈ Finset.Ico k (m - 1), (G ((i + 1 : ℕ) : ℝ) - G (i : ℝ)) * H i| := by
    have h1 : |G (((m - 1 : ℕ)) : ℝ) * H (m - 1) - G (k : ℝ) * H (k - 1)
        - ∑ i ∈ Finset.Ico k (m - 1), (G ((i + 1 : ℕ) : ℝ) - G (i : ℝ)) * H i|
        ≤ |G (((m - 1 : ℕ)) : ℝ) * H (m - 1) - G (k : ℝ) * H (k - 1)|
          + |∑ i ∈ Finset.Ico k (m - 1), (G ((i + 1 : ℕ) : ℝ) - G (i : ℝ)) * H i| :=
      abs_sub _ _
    have h2 : |G (((m - 1 : ℕ)) : ℝ) * H (m - 1) - G (k : ℝ) * H (k - 1)|
        ≤ |G (((m - 1 : ℕ)) : ℝ) * H (m - 1)| + |G (k : ℝ) * H (k - 1)| :=
      abs_sub _ _
    linarith [h1, h2]
  have hC' : |∑ i ∈ Finset.Ico k (m - 1), (G ((i + 1 : ℕ) : ℝ) - G (i : ℝ)) * H i|
      ≤ ε * ((k : ℝ) * G (k : ℝ) + ∑ i ∈ Finset.Ico k m, G (i : ℝ)) :=
    hC.trans (mul_le_mul_of_nonneg_left hT hε0)
  have hlin : |G (((m - 1 : ℕ)) : ℝ) * H (m - 1) - G (k : ℝ) * H (k - 1)
      - ∑ i ∈ Finset.Ico k (m - 1), (G ((i + 1 : ℕ) : ℝ) - G (i : ℝ)) * H i|
      ≤ ε * (((m : ℝ) * G (((m - 1 : ℕ)) : ℝ)) + ((k : ℝ) * G (k : ℝ))
        + ((k : ℝ) * G (k : ℝ) + ∑ i ∈ Finset.Ico k m, G (i : ℝ))) := by
    have hsum : ε * ((m : ℝ) * G (((m - 1 : ℕ)) : ℝ)) + ε * ((k : ℝ) * G (k : ℝ))
        + ε * ((k : ℝ) * G (k : ℝ) + ∑ i ∈ Finset.Ico k m, G (i : ℝ))
        = ε * (((m : ℝ) * G (((m - 1 : ℕ)) : ℝ)) + ((k : ℝ) * G (k : ℝ))
          + ((k : ℝ) * G (k : ℝ) + ∑ i ∈ Finset.Ico k m, G (i : ℝ))) := by ring
    linarith [htri, hA, hB, hC', hsum]
  refine hlin.trans ?_
  apply mul_le_mul_of_nonneg_left _ hε0
  have hk2 : (0 : ℝ) ≤ (k : ℝ) * G (k : ℝ) := mul_nonneg hk0 hgk
  have hm2 : (0 : ℝ) ≤ (m : ℝ) * G (((m - 1 : ℕ)) : ℝ) := mul_nonneg hm0 hgb
  linarith [hk2, hm2, hsum0]
/-- Left Riemann sums of an antitone function dominate its integral. -/
private theorem integral_le_sum_Ico {k b : ℕ} (hkb : k ≤ b) {G : ℝ → ℝ}
    (hanti : AntitoneOn G (Set.Icc (k : ℝ) (b : ℝ))) :
    (∫ t in (k : ℝ)..(b : ℝ), G t) ≤ ∑ i ∈ Finset.Ico k b, G (i : ℝ) :=
  AntitoneOn.integral_le_sum_Ico hkb hanti

/-- Left Riemann sums of an antitone nonnegative function are controlled by the integral. -/
private theorem sum_Ico_le_integral_add {k b : ℕ} (hkb : k ≤ b) {G : ℝ → ℝ}
    (hanti : AntitoneOn G (Set.Icc (k : ℝ) (b : ℝ)))
    (hnn : ∀ t ∈ Set.Icc (k : ℝ) (b : ℝ), 0 ≤ G t) :
    ∑ i ∈ Finset.Ico k b, G (i : ℝ) ≤ (∫ t in (k : ℝ)..(b : ℝ), G t) + G (k : ℝ) := by
  rcases lt_or_eq_of_le hkb with hlt | heq
  · have hstep : ∑ i ∈ Finset.Ico k b, G (i : ℝ) =
        G (k : ℝ) + ∑ i ∈ Finset.Ico (k + 1) b, G (i : ℝ) := by
      have hconsec : ∑ i ∈ Finset.Ico k (k + 1), G (i : ℝ) + ∑ i ∈ Finset.Ico (k + 1) b, G (i : ℝ)
          = ∑ i ∈ Finset.Ico k b, G (i : ℝ) :=
        Finset.sum_Ico_consecutive (f := fun i : ℕ => G (i : ℝ)) (m := k) (n := k + 1) (k := b)
          (by omega) (by omega)
      have hsingle : ∑ i ∈ Finset.Ico k (k + 1), G (i : ℝ) = G (k : ℝ) := by
        rw [Finset.sum_Ico_succ_top (le_refl k), Finset.Ico_self, Finset.sum_empty, zero_add]
      rw [← hconsec, hsingle]
    have hshift : ∑ i ∈ Finset.Ico (k + 1) b, G (i : ℝ) ≤
        ∑ i ∈ Finset.Ico k b, G ((i + 1 : ℕ) : ℝ) := by
      have hadd := Finset.sum_Ico_add' (fun j : ℕ => G ((j : ℝ))) k (b - 1) 1
      rw [show b - 1 + 1 = b by omega] at hadd
      rw [← hadd]
      have hsub : Finset.Ico k (b - 1) ⊆ Finset.Ico k b := by
        intro i hi
        simp only [Finset.mem_Ico] at hi ⊢
        omega
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => by
        simp only [Finset.mem_Ico] at hi
        have hk' : (k : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by
          have h1 : (k : ℝ) ≤ (i : ℝ) := by exact_mod_cast (by omega : k ≤ i)
          push_cast
          linarith
        have hb' : ((i + 1 : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast (by omega : i + 1 ≤ b)
        exact hnn _ ⟨hk', hb'⟩)
    have hInt : ∑ i ∈ Finset.Ico k b, G ((i + 1 : ℕ) : ℝ) ≤ ∫ t in (k : ℝ)..(b : ℝ), G t :=
      AntitoneOn.sum_le_integral_Ico hkb hanti
    rw [hstep]
    linarith [hshift.trans hInt]
  · subst heq
    simp only [Finset.Ico_self, Finset.sum_empty, intervalIntegral.integral_same, zero_add]
    exact hnn _ ⟨le_rfl, le_rfl⟩
/-! ### Batch 3: the substitution `z = log (N/t) / log t` and its monotonicity -/

/-- Derivative of the Buchstab substitution `t ↦ log (N/t) / log t`. -/
private theorem hasDerivAt_phi {N t : ℝ} (hN : 0 < N) (ht : 1 < t) :
    HasDerivAt (fun s : ℝ => Real.log (N / s) / Real.log s)
      (-(Real.log N) / (t * (Real.log t) ^ 2)) t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hN0 : N ≠ 0 := ne_of_gt hN
  have ht' : t ≠ 0 := ne_of_gt ht0
  have hlogt : (0 : ℝ) < Real.log t := Real.log_pos ht
  have hNt : N / t ≠ 0 := div_ne_zero hN0 ht'
  have hinv : HasDerivAt (fun s : ℝ => s⁻¹) (-(t ^ 2)⁻¹) t := hasDerivAt_inv ht'
  have hmul : HasDerivAt (fun s : ℝ => N * s⁻¹) (N * (-(t ^ 2)⁻¹)) t := hinv.const_mul N
  have hfun : (fun s : ℝ => N * s⁻¹) = fun s : ℝ => N / s := by
    funext s; rw [div_eq_mul_inv]
  rw [hfun] at hmul
  have h1 : HasDerivAt (fun s : ℝ => N / s) (-(N / t ^ 2)) t := by
    convert hmul using 1
    ring
  have h2 : HasDerivAt (fun s : ℝ => Real.log (N / s)) ((-(N / t ^ 2)) / (N / t)) t :=
    h1.log hNt
  have h3 : HasDerivAt (fun s : ℝ => Real.log s) (1 / t) t := by
    have h := Real.hasDerivAt_log ht'
    simpa [one_div] using h
  have h4 : HasDerivAt (fun s : ℝ => Real.log (N / s) / Real.log s)
      ((((-(N / t ^ 2)) / (N / t)) * Real.log t - Real.log (N / t) * (1 / t))
        / (Real.log t) ^ 2) t :=
    h2.div h3 (ne_of_gt hlogt)
  convert h4 using 1
  have hsplit : Real.log (N / t) = Real.log N - Real.log t := Real.log_div hN0 ht'
  rw [hsplit]
  field_simp
  ring

/-- The Buchstab substitution is antitone. -/
private theorem antitoneOn_phi {N : ℝ} (hN : 1 < N) {k b : ℝ} (hk : 1 < k) (hbN : b < N) :
    AntitoneOn (fun t : ℝ => Real.log (N / t) / Real.log t) (Set.Icc k b) := by
  intro s hs t ht hst
  obtain ⟨hks, -⟩ := hs
  obtain ⟨hkt, htb⟩ := ht
  have hs1 : 1 < s := lt_of_lt_of_le hk hks
  have ht1 : 1 < t := lt_of_lt_of_le hk hkt
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have htN : t < N := htb.trans_lt hbN
  have hsN : s < N := hst.trans_lt htN
  have hls : 0 < Real.log s := Real.log_pos hs1
  have hlt : 0 < Real.log t := Real.log_pos ht1
  have hApos : 0 < Real.log (N / t) := by
    rw [Real.log_div (by linarith) (by linarith)]
    have h : Real.log t < Real.log N := Real.log_lt_log ht0 htN
    linarith
  have h1 : Real.log (N / t) / Real.log t ≤ Real.log (N / t) / Real.log s :=
    div_le_div_of_nonneg_left hApos.le hls (Real.log_le_log hs0 hst)
  have h2 : Real.log (N / t) / Real.log s ≤ Real.log (N / s) / Real.log s := by
    apply div_le_div_of_nonneg_right _ hls.le
    apply Real.log_le_log (div_pos (by linarith) ht0)
    apply div_le_div_of_nonneg_left (le_of_lt (by linarith : (0 : ℝ) < N)) hs0 hst
  linarith

/-- The scalar inequality behind the antitonicity of `t ↦ 1/(t log²(N/t))`. -/
private theorem v_scalar {N s t : ℝ} (hs : 1 < s) (hst : s ≤ t) (htN : t < N)
    (hAt : 2 ≤ Real.log (N / t)) :
    s * (Real.log (N / s)) ^ 2 ≤ t * (Real.log (N / t)) ^ 2 := by
  rcases eq_or_lt_of_le hst with heq | hlt
  · subst heq
    exact le_rfl
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hN0 : 0 < N := by linarith
  have hApos : 0 < Real.log (N / t) := by linarith
  have hδ : 0 < Real.log (t / s) := Real.log_pos (by rw [lt_div_iff₀ hs0]; linarith)
  have hδ0 : 0 ≤ Real.log (t / s) := hδ.le
  have hteq : t = s * Real.exp (Real.log (t / s)) := by
    rw [Real.exp_log (by positivity)]
    field_simp
  have hlogdiv : Real.log (N / s) = Real.log (N / t) + Real.log (t / s) := by
    rw [Real.log_div (by linarith) (by linarith), Real.log_div (by linarith) (by linarith),
      Real.log_div (by linarith) (by linarith)]
    ring
  have hstep1 : 1 + Real.log (t / s) / Real.log (N / t) ≤ Real.exp (Real.log (t / s) / 2) := by
    have h1 : 1 + Real.log (t / s) / Real.log (N / t) ≤ 1 + Real.log (t / s) / 2 := by
      have := div_le_div_of_nonneg_left hδ0 (by norm_num : (0 : ℝ) < 2) hAt
      linarith
    have h2 : 1 + Real.log (t / s) / 2 ≤ Real.exp (Real.log (t / s) / 2) := by
      have := Real.add_one_le_exp (Real.log (t / s) / 2)
      linarith
    linarith
  have hpos1 : (0 : ℝ) ≤ 1 + Real.log (t / s) / Real.log (N / t) := by
    have := div_nonneg hδ0 hApos.le
    linarith
  have hsq : (Real.log (N / t) + Real.log (t / s)) ^ 2
      = (Real.log (N / t)) ^ 2 * (1 + Real.log (t / s) / Real.log (N / t)) ^ 2 := by
    field_simp
  have hexpsq : (Real.exp (Real.log (t / s) / 2)) ^ 2 = Real.exp (Real.log (t / s)) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  have hcore : (Real.log (N / t) + Real.log (t / s)) ^ 2
      ≤ Real.exp (Real.log (t / s)) * (Real.log (N / t)) ^ 2 := by
    rw [hsq, mul_comm (Real.exp _) ((Real.log (N / t)) ^ 2)]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    calc (1 + Real.log (t / s) / Real.log (N / t)) ^ 2
        ≤ (Real.exp (Real.log (t / s) / 2)) ^ 2 := pow_le_pow_left₀ hpos1 hstep1 2
      _ = Real.exp (Real.log (t / s)) := hexpsq
  calc s * (Real.log (N / s)) ^ 2
      = s * (Real.log (N / t) + Real.log (t / s)) ^ 2 := by rw [hlogdiv]
    _ ≤ s * (Real.exp (Real.log (t / s)) * (Real.log (N / t)) ^ 2) :=
        mul_le_mul_of_nonneg_left hcore hs0.le
    _ = (s * Real.exp (Real.log (t / s))) * (Real.log (N / t)) ^ 2 := by ring
    _ = t * (Real.log (N / t)) ^ 2 := by rw [← hteq]

/-- `t ↦ 1/(t log²(N/t))` is antitone on the band. -/
private theorem antitoneOn_v {N : ℝ} {k b : ℝ} (hk : 1 < k) (hbN : b < N)
    (hAb : 2 ≤ Real.log (N / b)) :
    AntitoneOn (fun t : ℝ => 1 / (t * (Real.log (N / t)) ^ 2)) (Set.Icc k b) := by
  intro s hs t ht hst
  obtain ⟨hks, hsb⟩ := hs
  obtain ⟨hkt, htb⟩ := ht
  have hs1 : 1 < s := lt_of_lt_of_le hk hks
  have ht1 : 1 < t := hs1.trans_le hst
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have htN : t < N := htb.trans_lt hbN
  have hAt : 2 ≤ Real.log (N / t) := by
    refine le_trans hAb ?_
    apply Real.log_le_log (div_pos (by linarith : (0 : ℝ) < N) (by linarith : (0 : ℝ) < b))
    apply div_le_div_of_nonneg_left (le_of_lt (by linarith : (0 : ℝ) < N)) ht0 htb
  have hmain : s * (Real.log (N / s)) ^ 2 ≤ t * (Real.log (N / t)) ^ 2 :=
    v_scalar hs1 hst htN hAt
  have hp1 : (0 : ℝ) < s * (Real.log (N / s)) ^ 2 := by
    have h : 0 < Real.log (N / s) := by
      rw [Real.log_div (by linarith) (by linarith)]
      have h2 : Real.log s < Real.log N := Real.log_lt_log hs0 (hst.trans_lt htN)
      linarith
    positivity
  exact one_div_le_one_div_of_le hp1 hmain

/-- `t ↦ 1/log t` is antitone above one. -/
private theorem antitoneOn_inv_log {k : ℝ} (hk : 1 < k) :
    AntitoneOn (fun t : ℝ => 1 / Real.log t) (Set.Ici k) := by
  intro s hs t ht hst
  have hs1 : 1 < s := lt_of_lt_of_le hk hs
  have ht1 : 1 < t := lt_of_lt_of_le hk ht
  exact one_div_le_one_div_of_le (Real.log_pos hs1) (Real.log_le_log (by linarith) hst)

/-- The Buchstab weight `1/(t log t log²(N/t))` is antitone on the band. -/
private theorem antitoneOn_vtilde {N : ℝ} {k b : ℝ} (hk : 1 < k) (hbN : b < N)
    (hAb : 2 ≤ Real.log (N / b)) :
    AntitoneOn (fun t : ℝ => 1 / (t * Real.log t * (Real.log (N / t)) ^ 2)) (Set.Icc k b) := by
  have hv := antitoneOn_v (N := N) (k := k) (b := b) hk hbN hAb
  have hl' : AntitoneOn (fun t : ℝ => 1 / Real.log t) (Set.Icc k b) :=
    (antitoneOn_inv_log hk).mono (fun x hx => hx.1)
  intro s hs t ht hst
  have hs1 : 1 < s := lt_of_lt_of_le hk hs.1
  have ht1 : 1 < t := lt_of_lt_of_le hk ht.1
  have h1 := hv hs ht hst
  have h2 := hl' hs ht hst
  have h3 : (0 : ℝ) ≤ 1 / Real.log t := (div_pos one_pos (Real.log_pos ht1)).le
  have h4 : (0 : ℝ) ≤ 1 / (s * (Real.log (N / s)) ^ 2) := by
    have hAlog : 0 < Real.log (N / s) := by
      rw [Real.log_div (by linarith [hs.2, hbN]) (by linarith)]
      have hltN : Real.log s < Real.log N := Real.log_lt_log (by linarith) (hs.2.trans_lt hbN)
      linarith
    positivity
  have hfun : ∀ x : ℝ, 1 / (x * Real.log x * (Real.log (N / x)) ^ 2)
      = (1 / (x * (Real.log (N / x)) ^ 2)) * (1 / Real.log x) := by
    intro x
    rw [div_mul_div_comm, mul_one]
    congr 1
    ring
  simp only [hfun]
  exact mul_le_mul h1 h2 h3 h4

/-- The Buchstab kernel weight is the derivative term of the substitution. -/
private theorem kernel_phi_mul_deriv {N t : ℝ} (hN : 1 < N) (ht : 1 < t) (htN : t < N) :
    Kernel616.kernel (Real.log (N / t) / Real.log t) * (Real.log N / (t * (Real.log t) ^ 2))
      = (Real.log N) ^ 2 * (1 / (t * Real.log t * (Real.log (N / t)) ^ 2)) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hlt : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hA : Real.log (N / t) = Real.log N - Real.log t :=
    Real.log_div (ne_of_gt hN0) (ne_of_gt ht0)
  have hApos : Real.log (N / t) ≠ 0 := by
    rw [hA]
    have h : Real.log t < Real.log N := Real.log_lt_log ht0 htN
    intro hh
    linarith
  unfold Kernel616.kernel
  rw [hA]
  field_simp
  ring

/-- The change of variables `z = log (N/t) / log t` for the Buchstab weight. -/
private theorem integral_phi_weight_eq {N : ℕ} (hN : 1 < N) {k b : ℕ} (hk : 2 ≤ k) (hkb : k ≤ b)
    (hbN : (b : ℝ) < (N : ℝ)) (U : ℝ → ℝ) :
    ∫ t in ((k : ℝ))..((b : ℝ)), U (Real.log ((N : ℝ) / t) / Real.log t)
        * (1 / (t * Real.log t * (Real.log ((N : ℝ) / t)) ^ 2))
      = (1 / (Real.log (N : ℝ)) ^ 2) *
        ∫ s in (Real.log ((N : ℝ) / (b : ℝ)) / Real.log (b : ℝ))..(Real.log ((N : ℝ) / (k : ℝ)) / Real.log (k : ℝ)), U s * Kernel616.kernel s := by
  have hNr : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos hNr
  have hkr : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkbr : (k : ℝ) ≤ (b : ℝ) := by exact_mod_cast hkb
  have hmem : ∀ x ∈ Set.uIcc ((k : ℝ)) ((b : ℝ)), (1 : ℝ) < x ∧ x < (N : ℝ) := by
    intro x hx
    rw [Set.uIcc_of_le hkbr] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2, hbN]⟩
  have hcont : ContinuousOn (fun t : ℝ => Real.log ((N : ℝ) / t) / Real.log t)
      (Set.uIcc ((k : ℝ)) ((b : ℝ))) := by
    have h1 : ContinuousOn (fun t : ℝ => Real.log ((N : ℝ) / t))
        (Set.uIcc ((k : ℝ)) ((b : ℝ))) := by
      apply ContinuousOn.log
      · exact continuousOn_const.div continuousOn_id (fun x hx => by
          have hx0 : (0 : ℝ) < x := by linarith [(hmem x hx).1]
          exact ne_of_gt hx0)
      · intro x hx
        have hx0 : (0 : ℝ) < x := by linarith [(hmem x hx).1]
        have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
        exact div_ne_zero (ne_of_gt hN0) (ne_of_gt hx0)
    have h2 : ContinuousOn (fun t : ℝ => Real.log t) (Set.uIcc ((k : ℝ)) ((b : ℝ))) := by
      apply ContinuousOn.log continuousOn_id
      intro x hx
      have hx0 : (0 : ℝ) < x := by linarith [(hmem x hx).1]
      exact ne_of_gt hx0
    exact h1.div h2 (fun x hx => by
      have hx1 : (1 : ℝ) < x := (hmem x hx).1
      exact (Real.log_pos hx1).ne')
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (f := fun t : ℝ => Real.log ((N : ℝ) / t) / Real.log t)
    (f' := fun t : ℝ => -(Real.log (N : ℝ)) / (t * (Real.log t) ^ 2))
    (g := fun s : ℝ => U s * Kernel616.kernel s)
    hcont
    (fun x hx => by
      rw [min_eq_left hkbr, max_eq_right hkbr] at hx
      exact hasDerivAt_phi (by linarith) (by linarith [hx.1]))
    (fun x hx => by
      rw [min_eq_left hkbr, max_eq_right hkbr] at hx
      have hx1 : (0 : ℝ) < x := by linarith [hx.1]
      have hlogx : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
      have hpos : 0 < x * (Real.log x) ^ 2 := by positivity
      rw [neg_div]
      exact neg_nonpos.mpr (div_nonneg hL.le hpos.le))
  have hcongr : ∫ x in ((k : ℝ))..((b : ℝ)),
      (U (Real.log ((N : ℝ) / x) / Real.log x) * Kernel616.kernel (Real.log ((N : ℝ) / x) / Real.log x))
        * (-(Real.log (N : ℝ)) / (x * (Real.log x) ^ 2))
      = -((Real.log (N : ℝ)) ^ 2) *
        ∫ x in ((k : ℝ))..((b : ℝ)),
          U (Real.log ((N : ℝ) / x) / Real.log x)
            * (1 / (x * Real.log x * (Real.log ((N : ℝ) / x)) ^ 2)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hkbr] at hx
    have hx1 : (1 : ℝ) < x := by linarith [hx.1]
    have hxN : x < (N : ℝ) := lt_of_le_of_lt hx.2 hbN
    have hid := kernel_phi_mul_deriv (N := (N : ℝ)) (t := x) hNr hx1 hxN
    have hstep : Kernel616.kernel (Real.log ((N : ℝ) / x) / Real.log x)
        * (Real.log (N : ℝ) / (x * (Real.log x) ^ 2))
        = (Real.log (N : ℝ)) ^ 2 * (1 / (x * Real.log x * (Real.log ((N : ℝ) / x)) ^ 2)) := hid
    calc (U (Real.log ((N : ℝ) / x) / Real.log x)
            * Kernel616.kernel (Real.log ((N : ℝ) / x) / Real.log x))
          * (-(Real.log (N : ℝ)) / (x * (Real.log x) ^ 2))
        = -((Real.log (N : ℝ)) ^ 2 *
            (U (Real.log ((N : ℝ) / x) / Real.log x)
              * (1 / (x * Real.log x * (Real.log ((N : ℝ) / x)) ^ 2)))) := by
          have hkey := hstep
          calc (U (Real.log ((N : ℝ) / x) / Real.log x)
                * Kernel616.kernel (Real.log ((N : ℝ) / x) / Real.log x))
              * (-(Real.log (N : ℝ)) / (x * (Real.log x) ^ 2))
              = -(U (Real.log ((N : ℝ) / x) / Real.log x)
                  * (Kernel616.kernel (Real.log ((N : ℝ) / x) / Real.log x)
                    * (Real.log (N : ℝ) / (x * (Real.log x) ^ 2)))) := by ring
            _ = -(U (Real.log ((N : ℝ) / x) / Real.log x)
                  * ((Real.log (N : ℝ)) ^ 2
                    * (1 / (x * Real.log x * (Real.log ((N : ℝ) / x)) ^ 2)))) := by rw [hkey]
            _ = -((Real.log (N : ℝ)) ^ 2 *
                  (U (Real.log ((N : ℝ) / x) / Real.log x)
                    * (1 / (x * Real.log x * (Real.log ((N : ℝ) / x)) ^ 2)))) := by ring
      _ = -((Real.log (N : ℝ)) ^ 2) *
            (U (Real.log ((N : ℝ) / x) / Real.log x)
              * (1 / (x * Real.log x * (Real.log ((N : ℝ) / x)) ^ 2))) := by ring
  simp only [Function.comp_def] at hsub
  rw [hcongr] at hsub
  have hL2 : (0 : ℝ) < (Real.log (N : ℝ)) ^ 2 := by positivity
  have hfin : (Real.log (N : ℝ)) ^ 2 *
      (∫ x in ((k : ℝ))..((b : ℝ)), U (Real.log ((N : ℝ) / x) / Real.log x)
        * (1 / (x * Real.log x * (Real.log ((N : ℝ) / x)) ^ 2)))
      = -(∫ s in (Real.log ((N : ℝ) / (k : ℝ)) / Real.log (k : ℝ))..(Real.log ((N : ℝ) / (b : ℝ)) / Real.log (b : ℝ)), U s * Kernel616.kernel s) := by
    have h := hsub
    rw [neg_mul] at h
    have h2 := congrArg Neg.neg h
    simpa using h2
  have hL2ne : (Real.log (N : ℝ)) ^ 2 ≠ 0 := ne_of_gt hL2
  rw [show (1 : ℝ) / (Real.log (N : ℝ)) ^ 2 *
      (∫ s in (Real.log ((N : ℝ) / (b : ℝ)) / Real.log (b : ℝ))..(Real.log ((N : ℝ) / (k : ℝ)) / Real.log (k : ℝ)), U s * Kernel616.kernel s)
      = (-(∫ s in (Real.log ((N : ℝ) / (k : ℝ)) / Real.log (k : ℝ))..(Real.log ((N : ℝ) / (b : ℝ)) / Real.log (b : ℝ)), U s * Kernel616.kernel s))
        / (Real.log (N : ℝ)) ^ 2 from by
        rw [intervalIntegral.integral_symm]
        ring]
  rw [eq_div_iff hL2ne, mul_comm]
  exact hfin

/-- LEAF P0072 p. 63 first lower display, after absorbing its stated error.
OPEN analytic sieve bound. -/
theorem seed_lower15 (T : ℝ) (hT : 0 < T)
    (hTpaper : HasProd (fun p : {p : ℕ // p.Prime ∧ 2 < p} =>
      ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2))) T) :
    Lower T 15 224.9997 := by
  sorry

/-- LEAF P0072 p. 63 second display. OPEN analytic sieve bound. -/
theorem seed_upper14 (T : ℝ) (hT : 0 < T)
    (hTpaper : HasProd (fun p : {p : ℕ // p.Prime ∧ 2 < p} =>
      ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2))) T) :
    Upper T 14 196.0022 := by
  sorry

/-- LEAF P0072 p. 63 third display. OPEN analytic sieve bound. -/
theorem seed_upper12 (T : ℝ) (hT : 0 < T)
    (hTpaper : HasProd (fun p : {p : ℕ // p.Prime ∧ 2 < p} =>
      ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2))) T) :
    Upper T 12 144.1328 := by
  sorry

/-- LEAF P0072 p. 63 fourth display. OPEN analytic sieve bound. -/
theorem seed_lower10 (T : ℝ) (hT : 0 < T)
    (hTpaper : HasProd (fun p : {p : ℕ // p.Prime ∧ 2 < p} =>
      ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2))) T) :
    Lower T 10 98 := by
  sorry

/-- LEAF P0072 p. 63 fifth display. OPEN analytic sieve bound. -/
theorem seed_upper10 (T : ℝ) (hT : 0 < T)
    (hTpaper : HasProd (fun p : {p : ℕ // p.Prime ∧ 2 < p} =>
      ((p : ℝ) - 1) ^ 2 / ((p : ℝ) * ((p : ℝ) - 2))) T) :
    Upper T 10 101.6 := by
  sorry




/-! ## Pass 3 (2026-11-19): assembly of the two transfer leaves -/

/-- The prime band is exactly the block of primes between the two integer cutoffs. -/
private theorem primeBand_eq_Ico {N : ℕ} {β α : ℝ} (hα1 : 1 ≤ α) (hβ : 0 < β) (hN : 1 ≤ N) :
    primeBand N (cutoff N β) (cutoff N α) =
      (Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊ + 1)).filter Nat.Prime := by
  ext p
  simp only [primeBand, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨-, hpp, hw, hz⟩
    refine ⟨⟨?_, ?_⟩, hpp⟩
    · rw [cutoff_eq_coe_succ] at hw; exact_mod_cast hw
    · rw [cutoff_eq_coe_succ] at hz; exact_mod_cast hz
  · rintro ⟨⟨h1, h2⟩, hpp⟩
    have hbN : ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) := by
      have h1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hα0 : (0 : ℝ) < α := by linarith
      have hle1 : (1 : ℝ) / α ≤ 1 := by
        rw [div_le_one hα0]; linarith
      have h2' : (N : ℝ) ^ ((1 : ℝ) / α) ≤ (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1R hle1
      calc ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / α) := Nat.floor_le (by positivity)
        _ ≤ (N : ℝ) := by simpa using h2'
    have hpN : p ≤ N := by
      have : p ≤ ⌊(N : ℝ) ^ (1 / α)⌋₊ := by omega
      exact_mod_cast (le_trans (by exact_mod_cast this : (p : ℝ) ≤ _) hbN)
    refine ⟨by nlinarith, hpp, ?_, ?_⟩
    · rw [cutoff_eq_coe_succ]; exact_mod_cast h1
    · rw [cutoff_eq_coe_succ]; exact_mod_cast h2

/-- A product of two nonnegative antitone functions on a set is antitone there. -/
private theorem antitoneOn_mul {s : Set ℝ} {f g : ℝ → ℝ}
    (hf : AntitoneOn f s) (hg : AntitoneOn g s)
    (hf0 : ∀ x ∈ s, 0 ≤ f x) (hg0 : ∀ x ∈ s, 0 ≤ g x) :
    AntitoneOn (fun x => f x * g x) s := by
  intro x hx y hy hxy
  have h1 : f y ≤ f x := hf hx hy hxy
  have h2 : g y ≤ g x := hg hx hy hxy
  exact mul_le_mul h1 h2 (hg0 y hy) (le_trans (hf0 y hy) h1)

/-- Composing a monotone function with an antitone one stays antitone. -/
private theorem antitoneOn_comp {s : Set ℝ} {φ : ℝ → ℝ} {U : ℝ → ℝ}
    (hU : Monotone U) (hφ : AntitoneOn φ s) : AntitoneOn (fun t => U (φ t)) s := by
  intro x hx y hy hxy
  exact hU (hφ hx hy hxy)

/-- A monotone function on the kernel domain is bounded by its two endpoint values. -/
private theorem mono_le_max {U : ℝ → ℝ} (hU : Monotone U) {t : ℝ}
    (ht : t ∈ Set.Icc (2 : ℝ) 14) : U t ≤ max (U 2) (U 14) :=
  (hU ht.2).trans (le_max_right _ _)

/-- On the band the Chebyshev increments carry the band sum to a `θ`-increment sum. -/
private theorem band_sum_eq_theta_sum {N : ℕ} {β α : ℝ} {f : ℝ → ℝ}
    (hα1 : 1 ≤ α) (hβ : 0 < β) (hN : 1 ≤ N)
    (hk2 : 2 ≤ ⌊(N : ℝ) ^ (1 / β)⌋₊ + 1)
    (hbN : ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) < (N : ℝ)) :
    ∑ p ∈ primeBand N (cutoff N β) (cutoff N α),
        f (Real.log ((N : ℝ) / p) / Real.log p) * (1 / ((p : ℝ) * (Real.log ((N : ℝ) / p)) ^ 2))
      = ∑ i ∈ Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊ + 1),
          (Chebyshev.theta (i : ℝ) - Chebyshev.theta (((i - 1 : ℕ)) : ℝ)) *
            (f (Real.log ((N : ℝ) / i) / Real.log i) *
              (1 / ((i : ℝ) * Real.log i * (Real.log ((N : ℝ) / i)) ^ 2))) := by
  classical
  rw [primeBand_eq_Ico (β := β) (α := α) hα1 hβ hN, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro i hi
  obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.mp hi
  have hk2' : 2 ≤ i := le_trans hk2 hi1
  have hi2r : (i : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by
    have : i ≤ ⌊(N : ℝ) ^ (1 / α)⌋₊ := by omega
    exact_mod_cast this
  have hiN : (i : ℝ) < (N : ℝ) := lt_of_le_of_lt hi2r hbN
  have hi0 : (0 : ℝ) < (i : ℝ) := by
    have : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (by omega : 0 < i)
    exact this
  have hlogi0 : (0 : ℝ) < Real.log i := Real.log_pos (by exact_mod_cast hk2')
  have hZpos : (0 : ℝ) < Real.log ((N : ℝ) / i) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hi0]
    linarith
  rw [theta_sub_theta_pred]
  by_cases hprime : i.Prime
  · rw [if_pos hprime, if_pos hprime]
    have h1 : ((i : ℝ)) ≠ 0 := ne_of_gt hi0
    have h2 : Real.log (i : ℝ) ≠ 0 := ne_of_gt hlogi0
    have h3 : Real.log ((N : ℝ) / i) ≠ 0 := ne_of_gt hZpos
    field_simp
  · rw [if_neg hprime, if_neg hprime]
    ring

/-! ### The two cutoffs under `φ`, and elementary size bounds -/

/-- `φ` at a power cutoff recovers the exponent minus one. -/
private theorem phi_rpow {N u : ℝ} (hN : 1 < N) (hu : 0 < u) :
    Real.log (N / N ^ (1 / u)) / Real.log (N ^ (1 / u)) = u - 1 := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hL : Real.log N ≠ 0 := (Real.log_pos hN).ne'
  have hratio : N / N ^ (1 / u) = N ^ (1 - 1 / u) := by
    rw [Real.rpow_sub hN0 (1 : ℝ) (1 / u), Real.rpow_one]
  have h1 : Real.log (N ^ (1 - 1 / u)) = (1 - 1 / u) * Real.log N := Real.log_rpow hN0 _
  have h2 : Real.log (N ^ (1 / u)) = (1 / u) * Real.log N := Real.log_rpow hN0 _
  have hu0 : u ≠ 0 := ne_of_gt hu
  rw [hratio, h1, h2]
  field_simp

/-- `φ` is at most `β - 1` at the lower integer cutoff. -/
private theorem phi_lower_cutoff_le {N β : ℝ} (hN : 1 < N) (hβ : 0 < β)
    {k : ℕ} (hk1 : 1 < k) (hkN : (k : ℝ) < N) (hkge : N ^ (1 / β) ≤ (k : ℝ)) :
    Real.log (N / k) / Real.log k ≤ β - 1 := by
  have h1 : (1 : ℝ) < N ^ (1 / β) := Real.one_lt_rpow hN (one_div_pos.mpr hβ)
  have hanti := antitoneOn_phi (N := N) hN (k := N ^ (1 / β)) (b := (k : ℝ)) h1 hkN
  have hle : Real.log (N / (k : ℝ)) / Real.log (k : ℝ) ≤
      Real.log (N / N ^ (1 / β)) / Real.log (N ^ (1 / β)) :=
    hanti ⟨le_rfl, hkge⟩ ⟨hkge, le_rfl⟩ hkge
  rw [phi_rpow hN hβ] at hle
  exact hle

/-- `φ` is at least `α - 1` at the integer cutoff just below `N^(1/α)`. -/
private theorem le_phi_upper_cutoff {N α : ℝ} (hN : 1 < N) (hα : 0 < α) (hα1 : 1 < α)
    {b : ℕ} (hb1 : 1 < b) (hbN : (b : ℝ) < N) (hble : (b : ℝ) ≤ N ^ (1 / α)) :
    α - 1 ≤ Real.log (N / b) / Real.log b := by
  have hb1r : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
  have hlt : N ^ (1 / α) < N := by
    have h := Real.rpow_lt_rpow_of_exponent_lt hN (show (1 : ℝ) / α < 1 by
      rw [div_lt_one hα]; linarith)
    simpa using h
  have hanti := antitoneOn_phi (N := N) hN (k := (b : ℝ)) (b := N ^ (1 / α)) hb1r hlt
  have hle : Real.log (N / N ^ (1 / α)) / Real.log (N ^ (1 / α)) ≤
      Real.log (N / (b : ℝ)) / Real.log (b : ℝ) :=
    hanti ⟨le_rfl, hble⟩ ⟨hble, le_rfl⟩ hble
  rw [phi_rpow hN hα] at hle
  exact hle

/-- A cube-root is far below its argument. -/
private theorem rpow_third_le {N : ℝ} (hN : 64 ≤ N) : N ^ ((1 : ℝ) / 3) ≤ N / 16 := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hu0 : 0 ≤ N ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hN0.le _
  have hub : (0 : ℝ) ≤ N / 16 := by linarith
  have hcube : (N ^ ((1 : ℝ) / 3)) ^ 3 = N := by
    have hexp : ((1 : ℝ) / 3) = (((3 : ℕ) : ℝ))⁻¹ := by norm_num
    rw [hexp]
    exact Real.rpow_inv_natCast_pow hN0.le (by norm_num : 3 ≠ 0)
  have hle : (N ^ ((1 : ℝ) / 3)) ^ 3 ≤ (N / 16) ^ 3 := by
    rw [hcube]
    nlinarith [hN, sq_nonneg N]
  exact (pow_le_pow_iff_left₀ hu0 hub (by norm_num : 3 ≠ 0)).mp hle

/-- The upper integer cutoff is a small fraction of `N`, so the band lies far below `N`. -/
private theorem upper_cutoff_le {N : ℕ} {α : ℝ} (hN : 64 ≤ N) (hα : 3 ≤ α) :
    ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) ≤ (N : ℝ) / 8 := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hNr : (64 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hα0 : (0 : ℝ) < α := by linarith
  have hexp : (1 : ℝ) / α ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num) hα
  have hle : (N : ℝ) ^ (1 / α) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by simpa using hexp)
  have h16 := rpow_third_le hNr
  have hfl : ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / α) :=
    Nat.floor_le (by positivity)
  push_cast
  linarith

/-- `log 8 ≥ 2`, the constant behind the weight-monotonicity threshold. -/
private theorem log_eight_ge_two : (2 : ℝ) ≤ Real.log 8 := by
  have h : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [h]
  nlinarith [Real.log_two_gt_d9]

/-- The lower cutoff is at least `N^(1/16)`, so its logarithm carries a `log N / 16`. -/
private theorem log_lower_cutoff_ge {N : ℕ} {β : ℝ} (hN : 1 ≤ N) (hβ : 0 < β)
    (hβ15 : β ≤ 15) :
    Real.log (N : ℝ) / 16 ≤ Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hexp : (1 : ℝ) / 16 ≤ 1 / β :=
    one_div_le_one_div_of_le hβ (by linarith)
  have hpow : (N : ℝ) ^ ((1 : ℝ) / 16) ≤ (N : ℝ) ^ (1 / β) :=
    Real.rpow_le_rpow_of_exponent_le hNr hexp
  have hfloor := Nat.lt_floor_add_one ((N : ℝ) ^ (1 / β))
  have hk : (N : ℝ) ^ ((1 : ℝ) / 16) ≤ ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hlog : Real.log ((N : ℝ) ^ ((1 : ℝ) / 16)) ≤
      Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) hk
  rw [Real.log_rpow hN0] at hlog
  rw [show (1 : ℝ) / 16 * Real.log (N : ℝ) = Real.log (N : ℝ) / 16 by ring] at hlog
  exact hlog

/-- `2 ≤ N^(1/u)` for `u ≤ 15` once `N` is large. -/
private theorem two_le_rpow {N : ℕ} {u : ℝ} (hN : 65536 ≤ N) (hu : 0 < u) (hu15 : u ≤ 15) :
    (2 : ℝ) ≤ (N : ℝ) ^ (1 / u) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  have hbase : (2 : ℝ) ^ u ≤ (N : ℝ) := by
    have h1 : (2 : ℝ) ^ u ≤ (2 : ℝ) ^ (15 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hu15
    have h2 : (2 : ℝ) ^ (15 : ℝ) = 32768 := by norm_num
    have h3 : (65536 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have h1 : ((2 : ℝ) ^ u) ^ (1 / u) ≤ (N : ℝ) ^ (1 / u) :=
    Real.rpow_le_rpow (by positivity) hbase (by positivity)
  have h2 : ((2 : ℝ) ^ u) ^ ((1 : ℝ) / u) = 2 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hb : u * ((1 : ℝ) / u) = 1 := by field_simp
    rw [hb, Real.rpow_one]
  rw [h2] at h1
  exact h1

/-- The lower integer cutoff is at least three. -/
private theorem lower_cutoff_ge_three {N : ℕ} {β : ℝ} (hN : 65536 ≤ N) (hβ : 0 < β)
    (hβ15 : β ≤ 15) : 3 ≤ ⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 := by
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by
    have : (1 : ℕ) ≤ N := by omega
    exact_mod_cast this
  have h2 : (2 : ℝ) ≤ (N : ℝ) ^ (1 / β) := two_le_rpow hN hβ hβ15
  have h2f : 2 ≤ ⌊(N : ℝ) ^ (1 / β)⌋₊ := Nat.le_floor h2
  omega

/-- The upper integer cutoff is at least two. -/
private theorem upper_cutoff_ge_two {N : ℕ} {α : ℝ} (hN : 65536 ≤ N) (hα : 3 ≤ α)
    (hα15 : α ≤ 15) : 2 ≤ ⌊(N : ℝ) ^ (1 / α)⌋₊ := by
  have h2 : (2 : ℝ) ≤ (N : ℝ) ^ (1 / α) := two_le_rpow hN (by linarith) hα15
  exact Nat.le_floor h2

/-- The upper integer cutoff stays well below `N`. -/
private theorem upper_cutoff_lt {N : ℕ} {α : ℝ} (hN : 65536 ≤ N) (hα : 3 ≤ α) :
    ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) < (N : ℝ) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  have hle : ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) ≤ (N : ℝ) / 8 :=
    upper_cutoff_le (by omega : 64 ≤ N) hα
  have hpos : (0 : ℝ) < (N : ℝ) / 8 := by linarith
  have : ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) / 8 := by
    have : ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast; linarith
    linarith
  linarith

/-- On the band the substitution variable `φ` stays in `[2, 14]`. -/
private theorem phi_mem {N : ℕ} {α β : ℝ} (hN : 65536 ≤ N) (hα : 3 ≤ α) (hαβ : α ≤ β)
    (hβ : 0 < β) (hβ15 : β ≤ 15) (hα15 : α ≤ 15) {t : ℝ}
    (htk : ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) ≤ t)
    (htm : t ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) :
    (2 : ℝ) ≤ Real.log ((N : ℝ) / t) / Real.log t ∧
      Real.log ((N : ℝ) / t) / Real.log t ≤ 14 := by
  have hNr : (1 : ℝ) < (N : ℝ) := by
    have : (1 : ℕ) < N := by omega
    exact_mod_cast this
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hN64' : (65536 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hk3 := lower_cutoff_ge_three (N := N) (β := β) hN hβ hβ15
  have hb2 := upper_cutoff_ge_two (N := N) (α := α) hN hα hα15
  have hbN := upper_cutoff_lt (N := N) (α := α) hN hα
  have hk1 : (1 : ℝ) < ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by
    have : (3 : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hk3
    linarith
  have ht1 : (1 : ℝ) < t := lt_of_lt_of_le hk1 htk
  have hk_le : (N : ℝ) ^ (1 / β) ≤ ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one ((N : ℝ) ^ (1 / β))
    push_cast
    linarith
  have hkN : ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) < (N : ℝ) := by
    have hcast : ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) =
        ((⌊(N : ℝ) ^ (1 / β)⌋₊ : ℕ) : ℝ) + 1 := by
      push_cast; ring
    rw [hcast]
    have hfloor : ((⌊(N : ℝ) ^ (1 / β)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / β) :=
      Nat.floor_le (by positivity)
    have hβ3 : (3 : ℝ) ≤ β := le_trans hα hαβ
    have hexp : (1 : ℝ) / β ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hβ3
    have hpow : (N : ℝ) ^ (1 / β) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hNr) hexp
    have h16 : (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (N : ℝ) / 16 :=
      rpow_third_le (by exact_mod_cast (by omega : 64 ≤ N))
    linarith
  have hb1 : (1 : ℝ) < ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by
    have : (2 : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hb2
    linarith
  have hb_le : ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / α) :=
    Nat.floor_le (by positivity)
  constructor
  · -- lower bound: α - 1 ≤ φ t
    have hanti := antitoneOn_phi (N := (N : ℝ)) hNr (k := t)
      (b := ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) ht1 hbN
    have hle : Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
        Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) ≤ Real.log ((N : ℝ) / t) / Real.log t :=
      hanti ⟨le_rfl, htm⟩ ⟨htm, le_rfl⟩ htm
    have hlo := le_phi_upper_cutoff (N := (N : ℝ)) (α := α) hNr (by linarith) (by linarith)
      (b := ⌊(N : ℝ) ^ (1 / α)⌋₊) (by omega) hbN hb_le
    linarith
  · -- upper bound: φ t ≤ β - 1 ≤ 14
    have htN : t < (N : ℝ) := lt_of_le_of_lt htm hbN
    have hanti := antitoneOn_phi (N := (N : ℝ)) hNr
      (k := ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) (b := t) hk1 htN
    have hle : Real.log ((N : ℝ) / t) / Real.log t ≤
        Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) /
          Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) :=
      hanti ⟨le_rfl, htk⟩ ⟨htk, le_rfl⟩ htk
    have hhi := phi_lower_cutoff_le (N := (N : ℝ)) (β := β) hNr hβ
      (k := ⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (by omega) hkN hk_le
    linarith

/-- The Buchstab weight on the band is nonnegative. -/
private theorem G_nonneg {N : ℕ} {α β : ℝ} (hN : 65536 ≤ N) (hα : 3 ≤ α) (hβ : 0 < β)
    (hβ15 : β ≤ 15) {f : ℝ → ℝ} (hfnn : ∀ z, 0 ≤ f z) {t : ℝ}
    (htk : ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) ≤ t)
    (htm : t ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ)) :
    0 ≤ f (Real.log ((N : ℝ) / t) / Real.log t) *
      (1 / (t * Real.log t * (Real.log ((N : ℝ) / t)) ^ 2)) := by
  have hk3 := lower_cutoff_ge_three (N := N) (β := β) hN hβ hβ15
  have ht2 : (2 : ℝ) < t := by
    have : (3 : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hk3
    linarith
  have hm8 : ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) ≤ (N : ℝ) / 8 :=
    upper_cutoff_le (by omega : 64 ≤ N) hα
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  have htN : t < (N : ℝ) := by linarith
  have h1 : (0 : ℝ) < Real.log t := Real.log_pos (by linarith)
  have h2 : (0 : ℝ) < Real.log ((N : ℝ) / t) := by
    apply Real.log_pos
    rw [one_lt_div (by linarith)]
    linarith
  exact mul_nonneg (hfnn _) (by positivity)

/-- The Buchstab weight `G` is antitone on the band. -/
private theorem G_antitone {N : ℕ} {α β : ℝ} (hN : 65536 ≤ N) (hα : 3 ≤ α) (hαβ : α ≤ β)
    (hα15 : α ≤ 15) (hβ : 0 < β) (hβ15 : β ≤ 15) {f : ℝ → ℝ} (hfmono : Monotone f)
    (hfnn : ∀ z, 0 ≤ f z) :
    AntitoneOn (fun t : ℝ => f (Real.log ((N : ℝ) / t) / Real.log t) *
        (1 / (t * Real.log t * (Real.log ((N : ℝ) / t)) ^ 2)))
      (Set.Icc (((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) - 1)
        ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ)) := by
  have hNr : (1 : ℝ) < (N : ℝ) := by
    have : (1 : ℕ) < N := by omega
    exact_mod_cast this
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hk3 := lower_cutoff_ge_three (N := N) (β := β) hN hβ hβ15
  have hk1 : (1 : ℝ) < ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) - 1 := by
    have : (3 : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hk3
    linarith
  have hm8 : ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) ≤ (N : ℝ) / 8 :=
    upper_cutoff_le (by omega : 64 ≤ N) hα
  have hm0 : (0 : ℝ) < ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) := by
    have h2 := upper_cutoff_ge_two (N := N) (α := α) hN hα hα15
    have h2' : (2 : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by exact_mod_cast h2
    have : (2 : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    linarith
  have hmN : ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) < (N : ℝ) := by linarith
  have hAb : (2 : ℝ) ≤ Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ)) := by
    have h8 : (8 : ℝ) ≤ (N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hm0]
      linarith
    refine log_eight_ge_two.trans ?_
    exact Real.log_le_log (by norm_num) h8
  have hantiφ : AntitoneOn (fun t : ℝ => f (Real.log ((N : ℝ) / t) / Real.log t))
      (Set.Icc (((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) - 1)
        ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ)) :=
    antitoneOn_comp hfmono (antitoneOn_phi (N := (N : ℝ)) hNr
      (k := ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) - 1)
      (b := ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ)) hk1 hmN)
  have hantiv : AntitoneOn (fun t : ℝ => 1 / (t * Real.log t * (Real.log ((N : ℝ) / t)) ^ 2))
      (Set.Icc (((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) - 1)
        ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ)) :=
    antitoneOn_vtilde (N := (N : ℝ))
      (k := ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) - 1)
      (b := ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ)) hk1 hmN hAb
  refine antitoneOn_mul hantiφ hantiv ?_ ?_
  · intro x hx
    exact hfnn _
  · intro x hx
    have hx1 : (1 : ℝ) < x := lt_of_lt_of_le hk1 hx.1
    have hxN : x < (N : ℝ) := lt_of_le_of_lt hx.2 hmN
    have hl1 : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hl2 : (0 : ℝ) < Real.log ((N : ℝ) / x) := by
      apply Real.log_pos
      rw [one_lt_div (by linarith)]
      linarith
    positivity

/-- The upper integer cutoff still carries a `log N / 16`. -/
private theorem log_upper_cutoff_ge {N : ℕ} {α : ℝ} (hN : 65536 ≤ N) (hα : 3 ≤ α)
    (hα15 : α ≤ 15) (hL : 167 ≤ Real.log (N : ℝ)) :
    Real.log (N : ℝ) / 16 ≤ Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by
  have hNr : (1 : ℝ) < (N : ℝ) := by
    have : (1 : ℕ) < N := by omega
    exact_mod_cast this
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hα0 : (0 : ℝ) < α := by linarith
  have hx2 : (2 : ℝ) ≤ (N : ℝ) ^ (1 / α) := two_le_rpow hN (by linarith) hα15
  have hhalf : (N : ℝ) ^ (1 / α) / 2 ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by
    have h1 : (N : ℝ) ^ (1 / α) - 1 < ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by
      have h := Nat.lt_floor_add_one ((N : ℝ) ^ (1 / α))
      push_cast at h ⊢
      linarith
    linarith
  have hpos : (0 : ℝ) < (N : ℝ) ^ (1 / α) / 2 := by linarith
  have hlog := Real.log_le_log hpos hhalf
  have hx0 : (0 : ℝ) < (N : ℝ) ^ (1 / α) := by positivity
  rw [Real.log_div (ne_of_gt hx0) (by norm_num : (2 : ℝ) ≠ 0), Real.log_rpow hN0] at hlog
  have hexp : (1 : ℝ) / 15 ≤ 1 / α := one_div_le_one_div_of_le hα0 hα15
  have hmul : (1 : ℝ) / 15 * Real.log (N : ℝ) ≤ 1 / α * Real.log (N : ℝ) :=
    mul_le_mul_of_nonneg_right hexp (le_of_lt (Real.log_pos hNr))
  have hlog2 : Real.log 2 < 0.6932 := lt_trans Real.log_two_lt_d9 (by norm_num)
  nlinarith

/-- The scaled Buchstab weight at a band point, against the kernel at `2`. -/
private theorem L2G_le {N : ℕ} {α β : ℝ} (hN : 65536 ≤ N) (hα : 3 ≤ α) (hαβ : α ≤ β)
    (hα15 : α ≤ 15) (hβ : 0 < β) (hβ15 : β ≤ 15) {f : ℝ → ℝ} (hfmono : Monotone f)
    (hfnn : ∀ z, 0 ≤ f z) {t : ℝ}
    (htk : ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) ≤ t)
    (htm : t ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) :
    (Real.log (N : ℝ)) ^ 2 * (f (Real.log ((N : ℝ) / t) / Real.log t) *
        (1 / (t * Real.log t * (Real.log ((N : ℝ) / t)) ^ 2)))
      ≤ max (f 2) (f 14) * (3 / 4) *
        (Real.log (N : ℝ) / (t * (Real.log t) ^ 2)) := by
  have hNr : (1 : ℝ) < (N : ℝ) := by
    have : (1 : ℕ) < N := by omega
    exact_mod_cast this
  have hk3 := lower_cutoff_ge_three (N := N) (β := β) hN hβ hβ15
  have ht1 : (1 : ℝ) < t := by
    have : (3 : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hk3
    linarith
  have hm8 : ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) ≤ (N : ℝ) / 8 :=
    upper_cutoff_le (by omega : 64 ≤ N) hα
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hm8' : ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) / 8 := by
    have hle : ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    linarith
  have htN : t < (N : ℝ) := by linarith
  obtain ⟨hφ2, hφ14⟩ := phi_mem (N := N) hN hα hαβ hβ hβ15 hα15 htk htm
  have hfM : f (Real.log ((N : ℝ) / t) / Real.log t) ≤ max (f 2) (f 14) :=
    mono_le_max hfmono ⟨hφ2, hφ14⟩
  have hkey := kernel_phi_mul_deriv (N := (N : ℝ)) hNr ht1 htN
  have h2k : Kernel616.kernel 2 = 3 / 4 := by
    unfold Kernel616.kernel
    norm_num
  have hkern : Kernel616.kernel (Real.log ((N : ℝ) / t) / Real.log t) ≤ 3 / 4 := by
    have h := Kernel616.kernel_antitone (a := (2 : ℝ)) (b := _) (by norm_num) hφ2
    linarith [h2k]
  have hX : (0 : ℝ) ≤ Real.log (N : ℝ) / (t * (Real.log t) ^ 2) := by
    have h1 : (0 : ℝ) < Real.log (N : ℝ) := Real.log_pos hNr
    have h2 : (0 : ℝ) < Real.log t := Real.log_pos ht1
    positivity
  have hMf0 : (0 : ℝ) ≤ max (f 2) (f 14) := le_trans (hfnn 14) (le_max_right _ _)
  have hprod : f (Real.log ((N : ℝ) / t) / Real.log t) *
      Kernel616.kernel (Real.log ((N : ℝ) / t) / Real.log t) ≤ max (f 2) (f 14) * (3 / 4) :=
    mul_le_mul hfM hkern (le_of_lt (Kernel616.kernel_pos (by linarith))) hMf0
  calc (Real.log (N : ℝ)) ^ 2 * (f (Real.log ((N : ℝ) / t) / Real.log t) *
        (1 / (t * Real.log t * (Real.log ((N : ℝ) / t)) ^ 2)))
      = f (Real.log ((N : ℝ) / t) / Real.log t) *
        ((Real.log (N : ℝ)) ^ 2 * (1 / (t * Real.log t * (Real.log ((N : ℝ) / t)) ^ 2))) := by
        ring
    _ = f (Real.log ((N : ℝ) / t) / Real.log t) *
        (Kernel616.kernel (Real.log ((N : ℝ) / t) / Real.log t) *
          (Real.log (N : ℝ) / (t * (Real.log t) ^ 2))) := by rw [hkey]
    _ = (f (Real.log ((N : ℝ) / t) / Real.log t) *
          Kernel616.kernel (Real.log ((N : ℝ) / t) / Real.log t)) *
          (Real.log (N : ℝ) / (t * (Real.log t) ^ 2)) := by ring
    _ ≤ (max (f 2) (f 14) * (3 / 4)) *
          (Real.log (N : ℝ) / (t * (Real.log t) ^ 2)) :=
        mul_le_mul_of_nonneg_right hprod hX
    _ = max (f 2) (f 14) * (3 / 4) *
          (Real.log (N : ℝ) / (t * (Real.log t) ^ 2)) := by ring
/-! ## Pass 4 (2026-11-20): closing the two transfer leaves

The band sum `Σ_p f (φ p) / (p log² (N/p))` is compared with the Buchstab integral
`∫ f K` over `[α-1, β-1]`, where `K z = (z+1)/z²`.  Only elementary facts are used
besides the uniform Chebyshev error of pass 2: `θ`-summation by parts, the Riemann
comparisons already proved, the change of variables of pass 3, and the size bounds
`log k, log b ≥ log N / 16`. -/

/-- `log N` eventually dominates any fixed constant. -/
private theorem eventually_log_ge (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, A ≤ Real.log (N : ℝ) :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop A)

/-- `C / log N` is eventually at most any fixed positive constant. -/
private theorem eventually_div_log_le (C c : ℝ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, C / Real.log (N : ℝ) ≤ c := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ => (Real.log (N : ℝ))⁻¹) atTop (nhds 0) :=
    hlog.inv_tendsto_atTop
  have hmul : Tendsto (fun N : ℕ => C * (Real.log (N : ℝ))⁻¹) atTop (nhds (C * 0)) :=
    hinv.const_mul C
  have h0 : Tendsto (fun N : ℕ => C / Real.log (N : ℝ)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hmul
  exact h0.eventually (eventually_le_nhds hc)

/-- The Buchstab kernel is nonnegative above `2`. -/
private theorem kernel_nonneg_of_two {z : ℝ} (hz : 2 ≤ z) : 0 ≤ Kernel616.kernel z := by
  unfold Kernel616.kernel
  have hz0 : (0 : ℝ) < z := by linarith
  positivity

/-- The Buchstab kernel is at most one above `2`. -/
private theorem kernel_le_one {z : ℝ} (hz : 2 ≤ z) : Kernel616.kernel z ≤ 1 := by
  unfold Kernel616.kernel
  have hz0 : (0 : ℝ) < z := by linarith
  rw [div_le_one (by positivity)]
  nlinarith

/-- The kernel is measurable (its values at zero are irrelevant). -/
private theorem measurable_kernel : Measurable Kernel616.kernel := by
  unfold Kernel616.kernel
  have h1 : Measurable fun z : ℝ => z + 1 := measurable_id.add measurable_const
  have h2 : Measurable fun z : ℝ => z ^ 2 := (continuous_id.pow 2).measurable
  have h : Measurable fun z : ℝ => (z + 1) * (z ^ 2)⁻¹ := h1.mul h2.inv
  simpa only [Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv] using h

/-- `2 ≤ N^(1/240)` once `N` is at least `2^240`. -/
private theorem two_le_rpow_240 {N : ℝ} (hN : (2 : ℝ) ^ (240 : ℝ) ≤ N) :
    (2 : ℝ) ≤ N ^ ((1 : ℝ) / 240) := by
  have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ (240 : ℝ) := by positivity
  have h := Real.rpow_le_rpow h0 hN (by norm_num : (0 : ℝ) ≤ 1 / 240)
  have h2 : ((2 : ℝ) ^ (240 : ℝ)) ^ ((1 : ℝ) / 240) = 2 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rwa [h2] at h

/-- The integer just below the lower cutoff already exceeds `N^(1/16)`. -/
private theorem rpow_16_le_lower_cutoff_pred {N : ℕ} (hN : (2 : ℝ) ^ (240 : ℝ) ≤ (N : ℝ))
    {β : ℝ} (hβ : 0 < β) (hβ15 : β ≤ 15) :
    (N : ℝ) ^ ((1 : ℝ) / 16) ≤ ((⌊(N : ℝ) ^ (1 / β)⌋₊ : ℕ) : ℝ) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by positivity) hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (240 : ℝ) := by
      have : (1 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) := by norm_num
      calc (1 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) := this
        _ ≤ (2 : ℝ) ^ (240 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    linarith
  have hx : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 16) := Real.one_le_rpow hN1 (by norm_num)
  have hx0 : (0 : ℝ) < (N : ℝ) ^ ((1 : ℝ) / 16) := lt_of_lt_of_le one_pos hx
  have hexp2 : (1 : ℝ) / 15 ≤ 1 / β := one_div_le_one_div_of_le hβ hβ15
  have h2 : (N : ℝ) ^ ((1 : ℝ) / 15) ≤ (N : ℝ) ^ (1 / β) :=
    Real.rpow_le_rpow_of_exponent_le hN1 hexp2
  have hsplit : (N : ℝ) ^ ((1 : ℝ) / 15) =
      (N : ℝ) ^ ((1 : ℝ) / 16) * (N : ℝ) ^ ((1 : ℝ) / 240) := by
    rw [← Real.rpow_add hN0]
    norm_num
  have h240 : (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 240) := two_le_rpow_240 hN
  have h3 : 2 * (N : ℝ) ^ ((1 : ℝ) / 16) ≤ (N : ℝ) ^ (1 / β) := by
    rw [hsplit] at h2
    nlinarith
  have h4 : (N : ℝ) ^ (1 / β) - 1 < ((⌊(N : ℝ) ^ (1 / β)⌋₊ : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one ((N : ℝ) ^ (1 / β))
    push_cast at h
    linarith
  nlinarith

/-- On `[2, 14]` the product of a monotone nonnegative function with the kernel is
interval integrable. -/
private theorem intervalIntegrable_mul_kernel {a b : ℝ} (ha : 2 ≤ a) (ha14 : a ≤ 14)
    (hb : 2 ≤ b) (hb14 : b ≤ 14) {f : ℝ → ℝ} (hf : Monotone f)
    (hf0 : ∀ z ∈ Set.Icc (2 : ℝ) 14, 0 ≤ f z) :
    IntervalIntegrable (fun z => f z * Kernel616.kernel z) MeasureTheory.volume a b := by
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun z => f z * Kernel616.kernel z)
      MeasureTheory.volume :=
    (hf.measurable.mul measurable_kernel).aestronglyMeasurable
  have hbound : ∀ z ∈ Set.Ioc (min a b) (max a b), ‖f z * Kernel616.kernel z‖ ≤ f 14 := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    have hzlo : (2 : ℝ) ≤ z := by
      rcases le_or_gt a b with hab | hba
      · rw [min_eq_left hab] at hz1; linarith
      · rw [min_eq_right (le_of_lt hba)] at hz1; linarith
    have hzhi : z ≤ 14 := by
      rcases le_or_gt a b with hab | hba
      · rw [max_eq_right hab] at hz2; linarith
      · rw [max_eq_left (le_of_lt hba)] at hz2; linarith
    have hfz0 : 0 ≤ f z := hf0 z ⟨hzlo, hzhi⟩
    have hfz : f z ≤ f 14 := hf hzhi
    have hk0 : 0 ≤ Kernel616.kernel z := kernel_nonneg_of_two hzlo
    have hk1 : Kernel616.kernel z ≤ 1 := kernel_le_one hzlo
    have hprod : f z * Kernel616.kernel z = ‖f z * Kernel616.kernel z‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hfz0 hk0)]
    rw [← hprod]
    have hstep1 : f z * Kernel616.kernel z ≤ f 14 * Kernel616.kernel z :=
      mul_le_mul_of_nonneg_right hfz hk0
    have hstep2 : f 14 * Kernel616.kernel z ≤ f 14 * 1 :=
      mul_le_mul_of_nonneg_left hk1 (hf0 14 ⟨by norm_num, le_rfl⟩)
    linarith
  rw [intervalIntegrable_iff]
  refine MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top hmeas.restrict (f 14) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with z hz
  exact hbound z hz

/-- A nonnegative function bounded by `C` on `[a, b]` has integral at most `C * (b - a)`. -/
private theorem integral_le_len_mul {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} {C : ℝ}
    (hfb : ∀ z ∈ Set.Icc a b, f z ≤ C)
    (hfi : IntervalIntegrable f MeasureTheory.volume a b) :
    (∫ z in a..b, f z) ≤ C * (b - a) := by
  have hconst : IntervalIntegrable (fun _ : ℝ => C) MeasureTheory.volume a b :=
    intervalIntegrable_const
  have h := intervalIntegral.integral_mono_on hab hfi hconst hfb
  have h2 : (∫ _z in a..b, C) = C * (b - a) := by
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  linarith [h, h2]

/-- The scaled Buchstab weight at a band point is `O (max (f 2) (f 14) / log N)`. -/
private theorem G_bound {N : ℕ} (hN64 : 65536 ≤ N) {α β : ℝ} (hα : 3 ≤ α) (hαβ : α ≤ β)
    (hα15 : α ≤ 15) (hβ : 0 < β) (hβ15 : β ≤ 15) {f : ℝ → ℝ} (hfmono : Monotone f)
    (hfnn : ∀ z, 0 ≤ f z) {t : ℝ}
    (htk : ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) ≤ t)
    (htm : t ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))
    (ht1 : (1 : ℝ) ≤ t) (hlogt : Real.log (N : ℝ) / 16 ≤ Real.log t) :
    (Real.log (N : ℝ)) ^ 2 * (f (Real.log ((N : ℝ) / t) / Real.log t) *
        (1 / (t * Real.log t * (Real.log ((N : ℝ) / t)) ^ 2)))
      ≤ 192 * max (f 2) (f 14) / Real.log (N : ℝ) := by
  have hNr : (1 : ℝ) < (N : ℝ) := by
    have : (1 : ℕ) < N := by omega
    exact_mod_cast this
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hL : (0 : ℝ) < Real.log (N : ℝ) := Real.log_pos hNr
  have hX0 : (0 : ℝ) ≤ max (f 2) (f 14) := le_trans (hfnn 14) (le_max_right _ _)
  have hmain := L2G_le hN64 hα hαβ hα15 hβ hβ15 hfmono hfnn htk htm
  have hlogt0 : (0 : ℝ) < Real.log t := lt_of_lt_of_le (by linarith) hlogt
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  have hden : (Real.log (N : ℝ)) ^ 2 / 256 ≤ t * (Real.log t) ^ 2 := by
    have hsq : (Real.log (N : ℝ) / 16) ^ 2 ≤ (Real.log t) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hlogt 2
    have hmul : t * (Real.log (N : ℝ) / 16) ^ 2 ≤ t * (Real.log t) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (le_of_lt ht0)
    have heq : t * (Real.log (N : ℝ) / 16) ^ 2 = (Real.log (N : ℝ)) ^ 2 / 256 * t := by
      field_simp
      ring
    rw [heq] at hmul
    nlinarith [hmul, ht1]
  have hratio : Real.log (N : ℝ) / (t * (Real.log t) ^ 2) ≤ 256 / Real.log (N : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hL]
    nlinarith [hden]
  calc (Real.log (N : ℝ)) ^ 2 * (f (Real.log ((N : ℝ) / t) / Real.log t) *
        (1 / (t * Real.log t * (Real.log ((N : ℝ) / t)) ^ 2)))
      ≤ max (f 2) (f 14) * (3 / 4) * (Real.log (N : ℝ) / (t * (Real.log t) ^ 2)) := hmain
    _ ≤ max (f 2) (f 14) * (3 / 4) * (256 / Real.log (N : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hratio
        exact mul_nonneg hX0 (by norm_num)
    _ = 192 * max (f 2) (f 14) / Real.log (N : ℝ) := by
        field_simp
        ring

/-- The same bound with the index weight `t` restored. -/
private theorem tG_bound {N : ℕ} (hN64 : 65536 ≤ N) {α β : ℝ} (hα : 3 ≤ α) (hαβ : α ≤ β)
    (hα15 : α ≤ 15) (hβ : 0 < β) (hβ15 : β ≤ 15) {f : ℝ → ℝ} (hfmono : Monotone f)
    (hfnn : ∀ z, 0 ≤ f z) {t : ℝ}
    (htk : ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) ≤ t)
    (htm : t ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))
    (ht1 : (1 : ℝ) ≤ t) (hlogt : Real.log (N : ℝ) / 16 ≤ Real.log t) :
    (Real.log (N : ℝ)) ^ 2 * (t * (f (Real.log ((N : ℝ) / t) / Real.log t) *
        (1 / (t * Real.log t * (Real.log ((N : ℝ) / t)) ^ 2))))
      ≤ 192 * max (f 2) (f 14) / Real.log (N : ℝ) := by
  have hNr : (1 : ℝ) < (N : ℝ) := by
    have : (1 : ℕ) < N := by omega
    exact_mod_cast this
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hL : (0 : ℝ) < Real.log (N : ℝ) := Real.log_pos hNr
  have hX0 : (0 : ℝ) ≤ max (f 2) (f 14) := le_trans (hfnn 14) (le_max_right _ _)
  have hmain := L2G_le hN64 hα hαβ hα15 hβ hβ15 hfmono hfnn htk htm
  have hlogt0 : (0 : ℝ) < Real.log t := lt_of_lt_of_le (by linarith) hlogt
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  have hden : (Real.log (N : ℝ)) ^ 2 / 256 ≤ (Real.log t) ^ 2 := by
    have hsq : (Real.log (N : ℝ) / 16) ^ 2 ≤ (Real.log t) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hlogt 2
    have heq : (Real.log (N : ℝ) / 16) ^ 2 = (Real.log (N : ℝ)) ^ 2 / 256 := by
      field_simp
      ring
    rw [heq] at hsq
    exact hsq
  have hratio : Real.log (N : ℝ) / (Real.log t) ^ 2 ≤ 256 / Real.log (N : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hL]
    nlinarith [hden]
  have key : t * (max (f 2) (f 14) * (3 / 4) * (Real.log (N : ℝ) / (t * (Real.log t) ^ 2)))
      = max (f 2) (f 14) * (3 / 4) * (Real.log (N : ℝ) / (Real.log t) ^ 2) := by
    field_simp
  calc (Real.log (N : ℝ)) ^ 2 * (t * (f (Real.log ((N : ℝ) / t) / Real.log t) *
        (1 / (t * Real.log t * (Real.log ((N : ℝ) / t)) ^ 2))))
      = t * ((Real.log (N : ℝ)) ^ 2 * (f (Real.log ((N : ℝ) / t) / Real.log t) *
          (1 / (t * Real.log t * (Real.log ((N : ℝ) / t)) ^ 2)))) := by ring
    _ ≤ t * (max (f 2) (f 14) * (3 / 4) * (Real.log (N : ℝ) / (t * (Real.log t) ^ 2))) :=
        mul_le_mul_of_nonneg_left hmain (le_of_lt ht0)
    _ = max (f 2) (f 14) * (3 / 4) * (Real.log (N : ℝ) / (Real.log t) ^ 2) := key
    _ ≤ max (f 2) (f 14) * (3 / 4) * (256 / Real.log (N : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hratio
        exact mul_nonneg hX0 (by norm_num)
    _ = 192 * max (f 2) (f 14) / Real.log (N : ℝ) := by
        field_simp
        ring

/-- Scalar assembly of the Buchstab transfer: the three weighted bounds together with the
Abel inequality give the sharp coefficient. -/
private theorem eps_assembly {Sθ SG KK MM SS J X L ε : ℝ}
    (hAbel : |Sθ - SG| ≤ ε * (4 * (KK + MM + SS)))
    (hK1 : L ^ 2 * KK ≤ 192 * X * L⁻¹) (hK2 : L ^ 2 * MM ≤ 384 * X * L⁻¹)
    (hS : L ^ 2 * SS ≤ J + 384 * X * L⁻¹) (hSG : L ^ 2 * SG ≤ J + 384 * X * L⁻¹)
    (hε0 : 0 ≤ ε) (hε64 : ε ≤ 1 / 64) (hXL : 0 ≤ X * L⁻¹) (hL2 : 0 ≤ L ^ 2) :
    L ^ 2 * Sθ ≤ J + 4 * ε * J + 500 * X * L⁻¹ := by
  have h1 : Sθ ≤ SG + ε * (4 * (KK + MM + SS)) := by
    have h := (abs_le.mp hAbel).2
    linarith
  have hdist : L ^ 2 * (KK + MM + SS) = L ^ 2 * KK + L ^ 2 * MM + L ^ 2 * SS := by ring
  have hE : L ^ 2 * (KK + MM + SS) ≤ J + 960 * X * L⁻¹ := by
    linarith [hdist, hK1, hK2, hS]
  have hstep : L ^ 2 * Sθ ≤ L ^ 2 * SG + 4 * ε * (L ^ 2 * (KK + MM + SS)) := by
    have h := mul_le_mul_of_nonneg_left h1 hL2
    have h3 : L ^ 2 * (SG + ε * (4 * (KK + MM + SS))) =
        L ^ 2 * SG + 4 * ε * (L ^ 2 * (KK + MM + SS)) := by ring
    linarith [h, h3]
  have hstep2 : 4 * ε * (L ^ 2 * (KK + MM + SS)) ≤ 4 * ε * (J + 960 * X * L⁻¹) :=
    mul_le_mul_of_nonneg_left hE (by linarith : (0 : ℝ) ≤ 4 * ε)
  have h4 : 4 * ε * (J + 960 * X * L⁻¹) ≤ 4 * ε * J + 60 * X * L⁻¹ := by
    have hEE : ε * (X * L⁻¹) ≤ (1 / 64) * (X * L⁻¹) :=
      mul_le_mul_of_nonneg_right hε64 hXL
    nlinarith [hEE, hε0, hXL]
  have h5 : 500 * X * L⁻¹ = 384 * X * L⁻¹ + 60 * X * L⁻¹ + 56 * X * L⁻¹ := by ring
  nlinarith [hstep, hstep2, h4, hSG, h5, hXL, hε0]

set_option maxHeartbeats 4000000 in
/-- The Buchstab band sum against a monotone nonnegative weight, compared with the
kernel integral.  This is the analytic heart of both transfer leaves. -/
private theorem char_sum_le {N : ℕ} (hN : (2 : ℝ) ^ (240 : ℝ) ≤ (N : ℝ))
    {α β : ℝ} (hα : 3 ≤ α) (hαβ : α ≤ β) (hα15 : α ≤ 15) (hβ : 0 < β) (hβ15 : β ≤ 15)
    {f : ℝ → ℝ} (hfmono : Monotone f) (hfnn : ∀ z, 0 ≤ f z)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε64 : ε ≤ 1 / 64)
    (hθ : ∀ t : ℝ, (N : ℝ) ^ ((1 : ℝ) / 16) ≤ t → |Chebyshev.theta t - t| ≤ ε * t)
    (hlogk : Real.log (N : ℝ) / 16 ≤ Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ))
    (hlogb : Real.log (N : ℝ) / 16 ≤ Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) :
    (Real.log (N : ℝ)) ^ 2 *
        (∑ p ∈ primeBand N (cutoff N β) (cutoff N α),
          f (Real.log ((N : ℝ) / p) / Real.log p) *
            (1 / ((p : ℝ) * (Real.log ((N : ℝ) / p)) ^ 2)))
      ≤ (∫ z in (α - 1)..(β - 1), f z * Kernel616.kernel z)
        + 4 * ε * (∫ z in (α - 1)..(β - 1), f z * Kernel616.kernel z)
        + 500 * (max (f 2) (f 14)) / Real.log (N : ℝ) := by
  classical
  have hN64 : 65536 ≤ N := by
    have h2 : ((65536 : ℕ) : ℝ) ≤ (N : ℝ) := by
      have h16 : ((65536 : ℕ) : ℝ) = (2 : ℝ) ^ (16 : ℝ) := by
        rw [show (16 : ℝ) = ((16 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
        norm_num
      rw [h16]
      exact le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)) hN
    exact_mod_cast h2
  have hNr : (1 : ℝ) < (N : ℝ) := by
    have : (1 : ℕ) < N := by omega
    exact_mod_cast this
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hL : (0 : ℝ) < Real.log (N : ℝ) := Real.log_pos hNr
  have hX0 : (0 : ℝ) ≤ max (f 2) (f 14) := le_trans (hfnn 14) (le_max_right _ _)
  have hJnn : (0 : ℝ) ≤ ∫ z in (α - 1)..(β - 1), f z * Kernel616.kernel z := by
    apply intervalIntegral.integral_nonneg (by linarith : α - 1 ≤ β - 1)
    intro z hz
    exact mul_nonneg (hfnn z) (kernel_nonneg_of_two (by linarith [hz.1]))
  have hsmall0 : (0 : ℝ) ≤ 500 * (max (f 2) (f 14)) / Real.log (N : ℝ) := by positivity
  rcases lt_or_ge (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊ + 1) with hlt | hge
  · -- nonempty band
    have hkb : ⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 ≤ ⌊(N : ℝ) ^ (1 / α)⌋₊ := by omega
    have hk3 : 3 ≤ ⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 := lower_cutoff_ge_three hN64 hβ hβ15
    have hbNlt : ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) < (N : ℝ) := upper_cutoff_lt hN64 hα
    set G : ℝ → ℝ := fun t => f (Real.log ((N : ℝ) / t) / Real.log t) *
      (1 / (t * Real.log t * (Real.log ((N : ℝ) / t)) ^ 2)) with hGdef
    have hband := band_sum_eq_theta_sum (N := N) (β := β) (α := α) (f := f)
      (by linarith : 1 ≤ α) hβ (by omega : 1 ≤ N) (by omega : 2 ≤ ⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) hbNlt
    -- the uniform theta error on the band
    have hkpred : ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) - 1 =
        ((⌊(N : ℝ) ^ (1 / β)⌋₊ : ℕ) : ℝ) := by push_cast; ring
    have hθ' : ∀ t : ℝ, ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) - 1 ≤ t →
        |Chebyshev.theta t - t| ≤ ε * t := by
      intro t ht
      apply hθ t
      have hr := rpow_16_le_lower_cutoff_pred (N := N) hN hβ hβ15
      rw [hkpred] at ht
      linarith
    -- monotonicity and nonnegativity of the weight
    have hGanti : AntitoneOn G (Set.Icc (((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) - 1)
        ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ)) := G_antitone hN64 hα hαβ hα15 hβ hβ15 hfmono hfnn
    have hGnn : ∀ t ∈ Set.Icc ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)
        ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ), 0 ≤ G t := by
      intro t ht
      exact G_nonneg hN64 hα hβ hβ15 hfnn ht.1 ht.2
    -- Abel summation
    have hAbel := abs_sum_theta_increment_sub_le (k := ⌊(N : ℝ) ^ (1 / β)⌋₊ + 1)
      (m := ⌊(N : ℝ) ^ (1 / α)⌋₊ + 1) (G := G) (ε := ε)
      (by omega : 2 ≤ ⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) hlt hε0 hGanti hGnn hθ'
    simp only [Nat.add_sub_cancel] at hAbel
    -- Riemann comparison and the substitution
    have hantiOn : AntitoneOn G (Set.Icc ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)
        ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) := by
      apply hGanti.mono
      intro x hx
      refine ⟨?_, ?_⟩
      · linarith [hx.1]
      · have : ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) := by
          push_cast; linarith
        linarith [hx.2]
    have hnnOn : ∀ t ∈ Set.Icc ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)
        ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ), 0 ≤ G t := by
      intro t ht
      refine hGnn t ⟨ht.1, ?_⟩
      have : ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast; linarith
      linarith [ht.2]
    have hRiem : (∑ i ∈ Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊),
        G (i : ℝ))
        ≤ (∫ t in ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)..((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ), G t)
          + G ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) :=
      sum_Ico_le_integral_add hkb hantiOn hnnOn
    have hsplit : (∑ i ∈ Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊ + 1),
        G (i : ℝ))
        = (∑ i ∈ Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊), G (i : ℝ))
          + G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) :=
      Finset.sum_Ico_succ_top (f := fun i : ℕ => G (i : ℝ)) hkb
    have hsubst : (∫ t in ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)..((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ), G t)
        = (1 / (Real.log (N : ℝ)) ^ 2) *
          ∫ s in (Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
              Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))..(Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) /
              Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)), f s * Kernel616.kernel s :=
      integral_phi_weight_eq (N := N) (by omega : 1 < N) (by omega : 2 ≤ ⌊(N : ℝ) ^ (1 / β)⌋₊ + 1)
        hkb hbNlt f
    -- the two endpoints of the substituted interval
    have hble : ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / α) := Nat.floor_le (by positivity)
    have hb1 : (1 : ℝ) < ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by
      have h2 := upper_cutoff_ge_two hN64 hα hα15
      have h2' : (2 : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by exact_mod_cast h2
      linarith
    have hkN : ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) < (N : ℝ) := by
      have hm8 : ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) ≤ (N : ℝ) / 8 :=
        upper_cutoff_le (by omega : 64 ≤ N) (hα.trans hαβ)
      have hN8 : (0 : ℝ) < (N : ℝ) / 8 := by linarith
      linarith
    have hkge : (N : ℝ) ^ (1 / β) ≤ ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by
      have h := Nat.lt_floor_add_one ((N : ℝ) ^ (1 / β))
      push_cast
      linarith
    have hk1 : (1 : ℝ) < ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by
      have h : (3 : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hk3
      linarith
    have hkbR : ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) ≤
        ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hkb
    have hca : α - 1 ≤ Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
        Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) :=
      le_phi_upper_cutoff (N := (N : ℝ)) (α := α) hNr (by linarith) (by linarith)
        (b := ⌊(N : ℝ) ^ (1 / α)⌋₊) (by omega) hbNlt hble
    have hbd : Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) /
        Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) ≤ β - 1 :=
      phi_lower_cutoff_le (N := (N : ℝ)) (β := β) hNr hβ
        (k := ⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (by omega) hkN hkge
    have hab : Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
        Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)
        ≤ Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) /
          Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by
      have hanti := antitoneOn_phi (N := (N : ℝ)) hNr
        (k := ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ))
        (b := ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) hk1 hbNlt
      exact hanti ⟨le_rfl, hkbR⟩ ⟨hkbR, le_rfl⟩ hkbR
    -- the integral over the substituted interval is dominated by the full Buchstab integral
    have hint_le :
        (∫ s in (Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
            Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))..(Real.log ((N : ℝ) /
              ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) /
              Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)), f s * Kernel616.kernel s)
          ≤ ∫ z in (α - 1)..(β - 1), f z * Kernel616.kernel z := by
      apply intervalIntegral.integral_mono_interval hca hab hbd
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with z hz
        exact mul_nonneg (hfnn z) (kernel_nonneg_of_two (by linarith [hz.1]))
      · exact intervalIntegrable_mul_kernel (by linarith : (2 : ℝ) ≤ α - 1)
          (by linarith : α - 1 ≤ 14) (by linarith : (2 : ℝ) ≤ β - 1)
          (by linarith : β - 1 ≤ 14) hfmono (fun z _ => hfnn z)
    -- the substitution, scaled by log² N
    have hL2subst : (Real.log (N : ℝ)) ^ 2 *
        (∫ t in ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)..((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ), G t)
        = ∫ s in (Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
            Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))..(Real.log ((N : ℝ) /
              ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) /
              Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)), f s * Kernel616.kernel s := by
      rw [hsubst]
      have hL2ne : (Real.log (N : ℝ)) ^ 2 ≠ 0 := ne_of_gt (by positivity)
      field_simp
    -- scaled weight bounds at the two endpoints
    have hGk : (Real.log (N : ℝ)) ^ 2 * G ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)
        ≤ 192 * max (f 2) (f 14) / Real.log (N : ℝ) :=
      G_bound hN64 hα hαβ hα15 hβ hβ15 hfmono hfnn (t := ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ))
        le_rfl hkbR (by linarith) hlogk
    have hGb : (Real.log (N : ℝ)) ^ 2 * G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)
        ≤ 192 * max (f 2) (f 14) / Real.log (N : ℝ) :=
      G_bound hN64 hα hαβ hα15 hβ hβ15 hfmono hfnn (t := ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))
        hkbR le_rfl (by linarith) hlogb
    have hKGk : (Real.log (N : ℝ)) ^ 2 *
        (((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) * G ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ))
        ≤ 192 * max (f 2) (f 14) / Real.log (N : ℝ) :=
      tG_bound hN64 hα hαβ hα15 hβ hβ15 hfmono hfnn (t := ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ))
        le_rfl hkbR (by linarith) hlogk
    have hKGb : (Real.log (N : ℝ)) ^ 2 *
        (((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) * G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))
        ≤ 384 * max (f 2) (f 14) / Real.log (N : ℝ) := by
      have h2b : ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) ≤
          2 * ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by
        have h := upper_cutoff_ge_two hN64 hα hα15
        push_cast
        have h' : (2 : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by exact_mod_cast h
        linarith
      have hGb0 : (0 : ℝ) ≤ G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) :=
        hGnn _ ⟨hkbR, by push_cast; linarith⟩
      have hL2 : (0 : ℝ) ≤ (Real.log (N : ℝ)) ^ 2 := sq_nonneg _
      have hbase : (Real.log (N : ℝ)) ^ 2 *
          (((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) * G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))
          ≤ 192 * max (f 2) (f 14) / Real.log (N : ℝ) :=
        tG_bound hN64 hα hαβ hα15 hβ hβ15 hfmono hfnn (t := ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))
          hkbR le_rfl (by linarith) hlogb
      calc (Real.log (N : ℝ)) ^ 2 *
            (((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) * G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))
          ≤ (Real.log (N : ℝ)) ^ 2 *
              (2 * (((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) * G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left (by
              have h1 : ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) * G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)
                  ≤ (2 * ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) *
                    G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) :=
                mul_le_mul_of_nonneg_right h2b hGb0
              have h2 : (2 * ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) *
                  G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)
                  = 2 * (((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) *
                    G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) := by ring
              linarith) hL2
        _ = 2 * ((Real.log (N : ℝ)) ^ 2 *
              (((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) * G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))) := by ring
        _ ≤ 2 * (192 * max (f 2) (f 14) / Real.log (N : ℝ)) := by linarith
        _ = 384 * max (f 2) (f 14) / Real.log (N : ℝ) := by ring
    -- the scaled band sum
    have hS : (Real.log (N : ℝ)) ^ 2 *
        (∑ i ∈ Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊ + 1), G (i : ℝ))
        ≤ (∫ z in (α - 1)..(β - 1), f z * Kernel616.kernel z)
          + 384 * max (f 2) (f 14) / Real.log (N : ℝ) := by
      have hR : (Real.log (N : ℝ)) ^ 2 *
          (∑ i ∈ Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊), G (i : ℝ))
          ≤ (∫ z in (α - 1)..(β - 1), f z * Kernel616.kernel z)
            + (Real.log (N : ℝ)) ^ 2 * G ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by
        have h := mul_le_mul_of_nonneg_left hRiem (sq_nonneg (Real.log (N : ℝ)))
        calc (Real.log (N : ℝ)) ^ 2 *
              (∑ i ∈ Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊), G (i : ℝ))
            ≤ (Real.log (N : ℝ)) ^ 2 *
                ((∫ t in ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)..((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ), G t)
                  + G ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) := h
          _ = (Real.log (N : ℝ)) ^ 2 *
                (∫ t in ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)..((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ), G t)
              + (Real.log (N : ℝ)) ^ 2 * G ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by ring
          _ ≤ (∫ z in (α - 1)..(β - 1), f z * Kernel616.kernel z)
              + (Real.log (N : ℝ)) ^ 2 * G ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by
            have := hL2subst
            linarith [hint_le, this]
      have hsp := hsplit
      have hdist2 : (Real.log (N : ℝ)) ^ 2 *
          ((∑ i ∈ Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊), G (i : ℝ))
            + G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))
          = (Real.log (N : ℝ)) ^ 2 *
              (∑ i ∈ Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊), G (i : ℝ))
            + (Real.log (N : ℝ)) ^ 2 * G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by ring
      have hsum384 : 192 * max (f 2) (f 14) / Real.log (N : ℝ) +
          192 * max (f 2) (f 14) / Real.log (N : ℝ)
          = 384 * max (f 2) (f 14) / Real.log (N : ℝ) := by ring
      rw [hsp]
      linarith [hdist2, hR, hGb, hGk, hsum384]
    -- assemble the error terms
    have hXL : (0 : ℝ) ≤ max (f 2) (f 14) / Real.log (N : ℝ) := by positivity
    have hL2sq : (0 : ℝ) ≤ (Real.log (N : ℝ)) ^ 2 := sq_nonneg _
    rw [hband]
    have hXL' : (0 : ℝ) ≤ max (f 2) (f 14) * (Real.log (N : ℝ))⁻¹ := by positivity
    exact eps_assembly hAbel hKGk hKGb hS hS hε0 hε64 hXL' hL2sq
  · -- empty band
    have hk3e : 3 ≤ ⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 := lower_cutoff_ge_three hN64 hβ hβ15
    have hband := band_sum_eq_theta_sum (N := N) (β := β) (α := α) (f := f)
      (by linarith : 1 ≤ α) hβ (by omega : 1 ≤ N) (by omega : 2 ≤ ⌊(N : ℝ) ^ (1 / β)⌋₊ + 1)
      (upper_cutoff_lt hN64 hα)
    have hempty : Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊ + 1) = ∅ :=
      Finset.Ico_eq_empty_iff.mpr (not_lt.mpr hge)
    rw [hband, hempty, Finset.sum_empty, mul_zero]
    have h1 : (0 : ℝ) ≤ 4 * ε * (∫ z in (α - 1)..(β - 1), f z * Kernel616.kernel z) :=
      mul_nonneg (by linarith) hJnn
    have h2 : (0 : ℝ) ≤ 500 * (max (f 2) (f 14)) / Real.log (N : ℝ) := hsmall0
    linarith [hJnn, h1, h2]

/-- The two substituted endpoints miss the ends of `[α-1, β-1]` only by `O (N^{-1/15})`. -/
private theorem phi_lower_gap {N : ℕ} (hN64 : 65536 ≤ N) {α : ℝ} (hα : 3 ≤ α) (hα15 : α ≤ 15)
    (hlogb : Real.log (N : ℝ) / 16 ≤ Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))
    (hb1 : (1 : ℝ) < ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))
    (hble : ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / α))
    (hL1 : (1 : ℝ) ≤ Real.log (N : ℝ))
    (hle : α - 1 ≤ Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
      Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) :
    Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
        Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) - (α - 1)
      ≤ 480 * (N : ℝ) ^ (-(1 / 15 : ℝ)) := by
  have hα0 : 0 < α := by linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  have hN64' : (65536 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN64
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  set x : ℝ := (N : ℝ) ^ (1 / α) with hxdef
  set b : ℝ := ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) with hbdef
  have hxpos : 0 < x := Real.rpow_pos_of_pos hN0 _
  have hb0 : 0 < b := lt_trans one_pos hb1
  have hbx : b ≤ x := hble
  have hxlt : x - 1 < b := by
    rw [hbdef, hxdef]
    have h := Nat.lt_floor_add_one ((N : ℝ) ^ (1 / α))
    push_cast
    linarith
  have hx2 : (2 : ℝ) ≤ x := two_le_rpow hN64 (by linarith) hα15
  have hxα : x ^ α = (N : ℝ) := by
    rw [hxdef, ← Real.rpow_mul (le_of_lt hN0), one_div,
      inv_mul_cancel₀ (ne_of_gt hα0), Real.rpow_one]
  have hlogN : Real.log (N : ℝ) = α * Real.log x := by
    rw [← hxα, Real.log_rpow hxpos]
  have hlogbpos : 0 < Real.log b := Real.log_pos hb1
  have hx1 : (1 : ℝ) < x := by linarith
  have hL0 : 0 < Real.log (N : ℝ) := by
    rw [hlogN]
    have := Real.log_pos hx1
    nlinarith
  have hkey : Real.log (N : ℝ) - α * Real.log b = α * Real.log (x / b) := by
    rw [hlogN]
    have hd : Real.log (x / b) = Real.log x - Real.log b :=
      Real.log_div (ne_of_gt hxpos) (ne_of_gt hb0)
    rw [hd]
    ring
  have hlogxb : Real.log (x / b) ≤ 2 / x := by
    have h1 : Real.log (x / b) ≤ x / b - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : x / b - 1 = (x - b) / b := by
      field_simp <;> ring
    have h3 : (x - b) / b ≤ 1 / b := by
      rw [div_le_div_iff₀ hb0 hb0]
      nlinarith
    have h4 : 1 / b ≤ 2 / x := by
      rw [div_le_div_iff₀ hb0 hxpos]
      nlinarith [hxlt, hx2]
    linarith
  have hdiff : Real.log (N : ℝ) - α * Real.log b ≤ α * (2 / x) := by
    rw [hkey]
    nlinarith [hlogxb, hα0]
  have hgapmul : (Real.log ((N : ℝ) / b) / Real.log b - (α - 1)) * Real.log b
      = Real.log (N : ℝ) - α * Real.log b := by
    rw [Real.log_div (ne_of_gt hN0) (ne_of_gt hb0)]
    field_simp <;> ring
  have hnn : 0 ≤ Real.log ((N : ℝ) / b) / Real.log b - (α - 1) := by linarith
  have hstep : (Real.log ((N : ℝ) / b) / Real.log b - (α - 1)) * Real.log b ≤ α * (2 / x) := by
    rw [hgapmul]
    exact hdiff
  have hgaple : Real.log ((N : ℝ) / b) / Real.log b - (α - 1) ≤ α * (2 / x) / Real.log b :=
    (le_div_iff₀ hlogbpos).mpr hstep
  have h16 : α * (2 / x) / Real.log b ≤ α * (2 / x) / (Real.log (N : ℝ) / 16) := by
    have hx' : 0 < α * (2 / x) := by positivity
    exact div_le_div_of_nonneg_left (le_of_lt hx') (by linarith) hlogb
  have hfin : α * (2 / x) / (Real.log (N : ℝ) / 16) = 32 * α / (x * Real.log (N : ℝ)) := by
    field_simp <;> ring
  have hxinv : x⁻¹ = (N : ℝ) ^ (-(1 / α)) := by
    rw [hxdef]
    exact (Real.rpow_neg (le_of_lt hN0) (1 / α)).symm
  have hle15 : (N : ℝ) ^ (-(1 / α)) ≤ (N : ℝ) ^ (-(1 / 15 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hN1
    have : (1 : ℝ) / 15 ≤ 1 / α := one_div_le_one_div_of_le hα0 hα15
    linarith
  have hfinal : 32 * α / (x * Real.log (N : ℝ)) ≤ 480 * (N : ℝ) ^ (-(1 / 15 : ℝ)) := by
    have hstep1 : 32 * α / (x * Real.log (N : ℝ)) ≤ 32 * α / x := by
      exact div_le_div_of_nonneg_left (by positivity) hxpos (by nlinarith)
    have hstep2 : 32 * α / x = 32 * α * (N : ℝ) ^ (-(1 / α)) := by
      rw [div_eq_mul_inv, hxinv]
    have hstep3 : 32 * α * (N : ℝ) ^ (-(1 / α)) ≤ 32 * 15 * (N : ℝ) ^ (-(1 / 15 : ℝ)) := by
      have h1 : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 / α)) := Real.rpow_nonneg (le_of_lt hN0) _
      nlinarith [hle15, h1, hα, hα15]
    linarith
  linarith [hgaple, h16, hfin, hfinal]

/-- The upper substituted endpoint misses `β - 1` only by `O (N^{-1/15})`. -/
private theorem phi_upper_gap {N : ℕ} (hN64 : 65536 ≤ N) {β : ℝ} (hβ : 0 < β) (hβ15 : β ≤ 15)
    (hlogk : Real.log (N : ℝ) / 16 ≤ Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ))
    (hk1 : (1 : ℝ) < ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ))
    (hkle : (N : ℝ) ^ (1 / β) ≤ ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ))
    (hL1 : (1 : ℝ) ≤ Real.log (N : ℝ))
    (hge : Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) /
      Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) ≤ β - 1) :
    (β - 1) - Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) /
        Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)
      ≤ 480 * (N : ℝ) ^ (-(1 / 15 : ℝ)) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  have hN64' : (65536 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN64
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  set y : ℝ := (N : ℝ) ^ (1 / β) with hydef
  set k : ℝ := ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) with hk
  have hypos : 0 < y := Real.rpow_pos_of_pos hN0 _
  have hk0 : 0 < k := lt_trans one_pos hk1
  have hky : y ≤ k := hkle
  have hky1 : k - 1 ≤ y := by
    rw [hk, hydef]
    have h' : ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) - 1 =
        ((⌊(N : ℝ) ^ (1 / β)⌋₊ : ℕ) : ℝ) := by
      push_cast
      ring
    rw [h']
    exact Nat.floor_le (by positivity)
  have hyβ : y ^ β = (N : ℝ) := by
    rw [hydef, ← Real.rpow_mul (le_of_lt hN0), one_div,
      inv_mul_cancel₀ (ne_of_gt hβ), Real.rpow_one]
  have hlogN : Real.log (N : ℝ) = β * Real.log y := by
    rw [← hyβ, Real.log_rpow hypos]
  have hlogkpos : 0 < Real.log k := Real.log_pos hk1
  have hkey : β * Real.log k - Real.log (N : ℝ) = β * Real.log (k / y) := by
    rw [hlogN]
    have hd : Real.log (k / y) = Real.log k - Real.log y :=
      Real.log_div (ne_of_gt hk0) (ne_of_gt hypos)
    rw [hd]
    ring
  have hlogky : Real.log (k / y) ≤ 2 / y := by
    have h1 : Real.log (k / y) ≤ k / y - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : k / y - 1 = (k - y) / y := by
      field_simp <;> ring
    have h3 : (k - y) / y ≤ 1 / y := by
      rw [div_le_div_iff₀ hypos hypos]
      nlinarith
    have h4 : 1 / y ≤ 2 / y := by
      rw [div_le_div_iff₀ hypos hypos]
      linarith
    linarith
  have hdiff : β * Real.log k - Real.log (N : ℝ) ≤ β * (2 / y) := by
    rw [hkey]
    nlinarith [hlogky, hβ]
  have hgapmul : ((β - 1) - Real.log ((N : ℝ) / k) / Real.log k) * Real.log k
      = β * Real.log k - Real.log (N : ℝ) := by
    rw [Real.log_div (ne_of_gt hN0) (ne_of_gt hk0)]
    field_simp <;> ring
  have hstep : ((β - 1) - Real.log ((N : ℝ) / k) / Real.log k) * Real.log k ≤ β * (2 / y) := by
    rw [hgapmul]
    exact hdiff
  have hgaple : (β - 1) - Real.log ((N : ℝ) / k) / Real.log k ≤ β * (2 / y) / Real.log k :=
    (le_div_iff₀ hlogkpos).mpr hstep
  have h16 : β * (2 / y) / Real.log k ≤ β * (2 / y) / (Real.log (N : ℝ) / 16) := by
    have hy' : 0 < β * (2 / y) := by positivity
    exact div_le_div_of_nonneg_left (le_of_lt hy') (by linarith) hlogk
  have hfin : β * (2 / y) / (Real.log (N : ℝ) / 16) = 32 * β / (y * Real.log (N : ℝ)) := by
    field_simp <;> ring
  have hyinv : y⁻¹ = (N : ℝ) ^ (-(1 / β)) := by
    rw [hydef]
    exact (Real.rpow_neg (le_of_lt hN0) (1 / β)).symm
  have hle15 : (N : ℝ) ^ (-(1 / β)) ≤ (N : ℝ) ^ (-(1 / 15 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hN1
    have : (1 : ℝ) / 15 ≤ 1 / β := one_div_le_one_div_of_le hβ hβ15
    linarith
  have hfinal : 32 * β / (y * Real.log (N : ℝ)) ≤ 480 * (N : ℝ) ^ (-(1 / 15 : ℝ)) := by
    have hstep1 : 32 * β / (y * Real.log (N : ℝ)) ≤ 32 * β / y := by
      exact div_le_div_of_nonneg_left (by positivity) hypos (by nlinarith)
    have hstep2 : 32 * β / y = 32 * β * (N : ℝ) ^ (-(1 / β)) := by
      rw [div_eq_mul_inv, hyinv]
    have hstep3 : 32 * β * (N : ℝ) ^ (-(1 / β)) ≤ 32 * 15 * (N : ℝ) ^ (-(1 / 15 : ℝ)) := by
      have h1 : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 / β)) := Real.rpow_nonneg (le_of_lt hN0) _
      nlinarith [hle15, h1, hβ, hβ15]
    linarith
  linarith [hgaple, h16, hfin, hfinal]

/-- Scalar assembly for the lower transfer: the Abel inequality is used in the lower
direction and the integral loses only the endpoint gaps. -/
private theorem eps_assembly_ge {Sθ SG KK MM SS J X L ε GAP : ℝ}
    (hAbel : |Sθ - SG| ≤ ε * (4 * (KK + MM + SS)))
    (hK1 : L ^ 2 * KK ≤ 192 * X * L⁻¹) (hK2 : L ^ 2 * MM ≤ 384 * X * L⁻¹)
    (hS : L ^ 2 * SS ≤ J + 384 * X * L⁻¹)
    (hSG : J - GAP ≤ L ^ 2 * SG)
    (hε0 : 0 ≤ ε) (hε64 : ε ≤ 1 / 64) (hXL : 0 ≤ X * L⁻¹) (hL2 : 0 ≤ L ^ 2) :
    J - 4 * ε * J - GAP - 500 * X * L⁻¹ ≤ L ^ 2 * Sθ := by
  have h1 : SG - ε * (4 * (KK + MM + SS)) ≤ Sθ := by
    have h := (abs_le.mp hAbel).1
    linarith
  have hdist : L ^ 2 * (KK + MM + SS) = L ^ 2 * KK + L ^ 2 * MM + L ^ 2 * SS := by ring
  have hE : L ^ 2 * (KK + MM + SS) ≤ J + 960 * X * L⁻¹ := by
    linarith [hdist, hK1, hK2, hS]
  have hstep : L ^ 2 * SG - 4 * ε * (L ^ 2 * (KK + MM + SS)) ≤ L ^ 2 * Sθ := by
    have h := mul_le_mul_of_nonneg_left h1 hL2
    have h3 : L ^ 2 * (SG - ε * (4 * (KK + MM + SS))) =
        L ^ 2 * SG - 4 * ε * (L ^ 2 * (KK + MM + SS)) := by ring
    linarith [h, h3]
  have hstep2 : 4 * ε * (L ^ 2 * (KK + MM + SS)) ≤ 4 * ε * (J + 960 * X * L⁻¹) :=
    mul_le_mul_of_nonneg_left hE (by linarith : (0 : ℝ) ≤ 4 * ε)
  have h4 : 4 * ε * (J + 960 * X * L⁻¹) ≤ 4 * ε * J + 60 * X * L⁻¹ := by
    have hEE : ε * (X * L⁻¹) ≤ (1 / 64) * (X * L⁻¹) :=
      mul_le_mul_of_nonneg_right hε64 hXL
    nlinarith [hEE, hε0, hXL]
  have h5 : (0 : ℝ) ≤ 500 * X * L⁻¹ - 60 * X * L⁻¹ := by
    have : (0 : ℝ) ≤ X * L⁻¹ := hXL
    nlinarith
  linarith [hstep, hstep2, h4, hSG, h5]

set_option maxHeartbeats 4000000 in
/-- The mirror of `char_sum_le`: the Buchstab band sum dominates the kernel integral up to
the two endpoint gaps and the Abel error. -/
private theorem char_sum_ge {N : ℕ} (hN : (2 : ℝ) ^ (240 : ℝ) ≤ (N : ℝ))
    {α β : ℝ} (hα : 3 ≤ α) (hαβ : α ≤ β) (hα15 : α ≤ 15) (hβ : 0 < β) (hβ15 : β ≤ 15)
    {f : ℝ → ℝ} (hfmono : Monotone f) (hfnn : ∀ z, 0 ≤ f z)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε64 : ε ≤ 1 / 64)
    (hθ : ∀ t : ℝ, (N : ℝ) ^ ((1 : ℝ) / 16) ≤ t → |Chebyshev.theta t - t| ≤ ε * t)
    (hlogk : Real.log (N : ℝ) / 16 ≤ Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ))
    (hlogb : Real.log (N : ℝ) / 16 ≤ Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))
    (hgap1 : Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
        Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) - (α - 1)
        ≤ 480 * (N : ℝ) ^ (-(1 / 15 : ℝ)))
    (hgap2 : (β - 1) - Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) /
        Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)
        ≤ 480 * (N : ℝ) ^ (-(1 / 15 : ℝ)))
    (hlt : ⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 < ⌊(N : ℝ) ^ (1 / α)⌋₊ + 1) :
    (∫ z in (α - 1)..(β - 1), f z * Kernel616.kernel z)
        - 4 * ε * (∫ z in (α - 1)..(β - 1), f z * Kernel616.kernel z)
        - 960 * (max (f 2) (f 14)) * (N : ℝ) ^ (-(1 / 15 : ℝ))
        - 500 * (max (f 2) (f 14)) * (Real.log (N : ℝ))⁻¹
      ≤ (Real.log (N : ℝ)) ^ 2 *
        (∑ p ∈ primeBand N (cutoff N β) (cutoff N α),
          f (Real.log ((N : ℝ) / p) / Real.log p) *
            (1 / ((p : ℝ) * (Real.log ((N : ℝ) / p)) ^ 2))) := by
  classical
  have hN64 : 65536 ≤ N := by
    have h2 : ((65536 : ℕ) : ℝ) ≤ (N : ℝ) := by
      have h16 : ((65536 : ℕ) : ℝ) = (2 : ℝ) ^ (16 : ℝ) := by
        rw [show (16 : ℝ) = ((16 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
        norm_num
      rw [h16]
      exact le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)) hN
    exact_mod_cast h2
  have hNr : (1 : ℝ) < (N : ℝ) := by
    have : (1 : ℕ) < N := by omega
    exact_mod_cast this
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hL : (0 : ℝ) < Real.log (N : ℝ) := Real.log_pos hNr
  have hX0 : (0 : ℝ) ≤ max (f 2) (f 14) := le_trans (hfnn 14) (le_max_right _ _)
  set X : ℝ := max (f 2) (f 14) with hXdef
  set J : ℝ := ∫ z in (α - 1)..(β - 1), f z * Kernel616.kernel z with hJdef
  have hkb : ⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 ≤ ⌊(N : ℝ) ^ (1 / α)⌋₊ := by omega
  have hk3 : 3 ≤ ⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 := lower_cutoff_ge_three hN64 hβ hβ15
  have hbNlt : ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) < (N : ℝ) := upper_cutoff_lt hN64 hα
  set G : ℝ → ℝ := fun t => f (Real.log ((N : ℝ) / t) / Real.log t) *
    (1 / (t * Real.log t * (Real.log ((N : ℝ) / t)) ^ 2)) with hGdef
  have hband := band_sum_eq_theta_sum (N := N) (β := β) (α := α) (f := f)
    (by linarith : 1 ≤ α) hβ (by omega : 1 ≤ N) (by omega : 2 ≤ ⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) hbNlt
  have hkpred : ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) - 1 =
      ((⌊(N : ℝ) ^ (1 / β)⌋₊ : ℕ) : ℝ) := by push_cast; ring
  have hθ' : ∀ t : ℝ, ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) - 1 ≤ t →
      |Chebyshev.theta t - t| ≤ ε * t := by
    intro t ht
    apply hθ t
    have hr := rpow_16_le_lower_cutoff_pred (N := N) hN hβ hβ15
    rw [hkpred] at ht
    linarith
  have hGanti : AntitoneOn G (Set.Icc (((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) - 1)
      ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ)) := G_antitone hN64 hα hαβ hα15 hβ hβ15 hfmono hfnn
  have hGnn : ∀ t ∈ Set.Icc ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)
      ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ), 0 ≤ G t := by
    intro t ht
    exact G_nonneg hN64 hα hβ hβ15 hfnn ht.1 ht.2
  have hAbel := abs_sum_theta_increment_sub_le (k := ⌊(N : ℝ) ^ (1 / β)⌋₊ + 1)
    (m := ⌊(N : ℝ) ^ (1 / α)⌋₊ + 1) (G := G) (ε := ε)
    (by omega : 2 ≤ ⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) hlt hε0 hGanti hGnn hθ'
  simp only [Nat.add_sub_cancel] at hAbel
  have hantiOn : AntitoneOn G (Set.Icc ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)
      ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) := by
    apply hGanti.mono
    intro x hx
    refine ⟨?_, ?_⟩
    · linarith [hx.1]
    · have : ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast; linarith
      linarith [hx.2]
  have hRiem : (∫ t in ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)..((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ), G t)
      ≤ ∑ i ∈ Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊), G (i : ℝ) :=
    integral_le_sum_Ico hkb hantiOn
  have hsplit : (∑ i ∈ Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊ + 1),
      G (i : ℝ))
      = (∑ i ∈ Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊), G (i : ℝ))
        + G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) :=
    Finset.sum_Ico_succ_top (f := fun i : ℕ => G (i : ℝ)) hkb
  have hsubst : (∫ t in ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)..((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ), G t)
      = (1 / (Real.log (N : ℝ)) ^ 2) *
        ∫ s in (Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
            Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))..(Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) /
            Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)), f s * Kernel616.kernel s :=
    integral_phi_weight_eq (N := N) (by omega : 1 < N) (by omega : 2 ≤ ⌊(N : ℝ) ^ (1 / β)⌋₊ + 1)
      hkb hbNlt f
  have hL2subst : (Real.log (N : ℝ)) ^ 2 *
      (∫ t in ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)..((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ), G t)
      = ∫ s in (Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
          Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))..(Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) /
          Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)), f s * Kernel616.kernel s := by
    rw [hsubst]
    have hL2ne : (Real.log (N : ℝ)) ^ 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp
  -- the endpoints of the substituted interval
  have hble : ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / α) := Nat.floor_le (by positivity)
  have hb1 : (1 : ℝ) < ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by
    have h2 := upper_cutoff_ge_two hN64 hα hα15
    have h2' : (2 : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by exact_mod_cast h2
    linarith
  have hkN : ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) < (N : ℝ) := by
    have hm8 : ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) ≤ (N : ℝ) / 8 :=
      upper_cutoff_le (by omega : 64 ≤ N) (hα.trans hαβ)
    have hN8 : (0 : ℝ) < (N : ℝ) / 8 := by linarith
    linarith
  have hkge : (N : ℝ) ^ (1 / β) ≤ ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one ((N : ℝ) ^ (1 / β))
    push_cast
    linarith
  have hk1 : (1 : ℝ) < ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by
    have h : (3 : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hk3
    linarith
  have hkbR : ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) ≤
      ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hkb
  have hca : α - 1 ≤ Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
      Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) :=
    le_phi_upper_cutoff (N := (N : ℝ)) (α := α) hNr (by linarith) (by linarith)
      (b := ⌊(N : ℝ) ^ (1 / α)⌋₊) (by omega) hbNlt hble
  have hbd : Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) /
      Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) ≤ β - 1 :=
    phi_lower_cutoff_le (N := (N : ℝ)) (β := β) hNr hβ
      (k := ⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (by omega) hkN hkge
  have hab : Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
      Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)
      ≤ Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) /
        Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by
    have hanti := antitoneOn_phi (N := (N : ℝ)) hNr
      (k := ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ))
      (b := ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) hk1 hbNlt
    exact hanti ⟨le_rfl, hkbR⟩ ⟨hkbR, le_rfl⟩ hkbR
  -- integrability on every subinterval
  have hInt := fun (a b : ℝ) (ha : 2 ≤ a) (ha14 : a ≤ 14) (hb : 2 ≤ b) (hb14 : b ≤ 14) =>
    intervalIntegrable_mul_kernel ha ha14 hb hb14 hfmono (fun z _ => hfnn z)
  have hφb2 : (2 : ℝ) ≤ Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
      Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) :=
    le_trans (by linarith : (2 : ℝ) ≤ α - 1) hca
  have hφk14 : Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) /
      Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) ≤ 14 :=
    le_trans hbd (by linarith : β - 1 ≤ 14)
  -- bound the two boundary pieces
  have hbnd : ∀ (a b : ℝ) (hab : a ≤ b) (ha : 2 ≤ a) (ha14 : a ≤ 14) (hb : 2 ≤ b) (hb14 : b ≤ 14),
      (∫ z in a..b, f z * Kernel616.kernel z) ≤ X * (b - a) := by
    intro a b hab ha ha14 hb hb14
    have hfzb : ∀ z ∈ Set.Icc a b, f z * Kernel616.kernel z ≤ X := by
      intro z hz
      have hz2 : (2 : ℝ) ≤ z := le_trans ha hz.1
      have hz14 : z ≤ 14 := le_trans hz.2 hb14
      have hfz : f z ≤ X := by
        rw [hXdef]
        exact (hfmono hz14).trans (le_max_right _ _)
      have hkz : Kernel616.kernel z ≤ 1 := kernel_le_one hz2
      have hkz0 : (0 : ℝ) ≤ Kernel616.kernel z := kernel_nonneg_of_two hz2
      have hfz0 : (0 : ℝ) ≤ f z := hfnn z
      have h1 : f z * Kernel616.kernel z ≤ X * Kernel616.kernel z :=
        mul_le_mul_of_nonneg_right hfz hkz0
      have h2 : X * Kernel616.kernel z ≤ X * 1 := mul_le_mul_of_nonneg_left hkz hX0
      linarith
    exact integral_le_len_mul hab (C := X) hfzb (hInt a b ha ha14 hb hb14)
  have hint_ge : J - 960 * X * (N : ℝ) ^ (-(1 / 15 : ℝ))
      ≤ ∫ s in (Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
          Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))..(Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) /
          Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)), f s * Kernel616.kernel s := by
    -- split the full integral at the two endpoints
    have hsplit1 : (∫ z in (α - 1)..(Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
        Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)), f z * Kernel616.kernel z)
        + ∫ z in (Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
            Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))..(β - 1), f z * Kernel616.kernel z
        = ∫ z in (α - 1)..(β - 1), f z * Kernel616.kernel z :=
      intervalIntegral.integral_add_adjacent_intervals
        (hInt (α - 1) _ (by linarith) (by linarith) (by linarith) (by linarith))
        (hInt _ (β - 1) (by linarith) (by linarith) (by linarith) (by linarith))
    have hsplit2 : (∫ z in (Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
        Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))..(Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) /
        Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)), f z * Kernel616.kernel z)
        + ∫ z in (Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) /
            Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ))..(β - 1), f z * Kernel616.kernel z
        = ∫ z in (Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
            Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))..(β - 1), f z * Kernel616.kernel z :=
      intervalIntegral.integral_add_adjacent_intervals
        (hInt _ _ (by linarith) (by linarith) (by linarith) (by linarith))
        (hInt _ (β - 1) (by linarith) (by linarith) (by linarith) (by linarith))
    have hb1' : (∫ z in (α - 1)..(Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
        Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)), f z * Kernel616.kernel z)
        ≤ X * ((Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
          Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) - (α - 1)) :=
      hbnd (α - 1) _ hca (by linarith) (by linarith) hφb2 (by linarith)
    have hb2' : (∫ z in (Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) /
        Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ))..(β - 1), f z * Kernel616.kernel z)
        ≤ X * ((β - 1) - (Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) /
          Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ))) :=
      hbnd _ (β - 1) hbd (by linarith) hφk14 (by linarith) (by linarith)
    have hgapb1 : (Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
        Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) - (α - 1) ≤ 480 * (N : ℝ) ^ (-(1 / 15 : ℝ)) :=
      hgap1
    have hgapb2 : (β - 1) - (Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) /
        Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) ≤ 480 * (N : ℝ) ^ (-(1 / 15 : ℝ)) :=
      hgap2
    have hsum : (∫ z in (α - 1)..(Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
        Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)), f z * Kernel616.kernel z)
        + ∫ z in (Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) /
            Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ))..(β - 1), f z * Kernel616.kernel z
        ≤ 960 * X * (N : ℝ) ^ (-(1 / 15 : ℝ)) := by
      have h1 : X * (Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
          Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) - (α - 1))
          ≤ X * (480 * (N : ℝ) ^ (-(1 / 15 : ℝ))) :=
        mul_le_mul_of_nonneg_left hgapb1 hX0
      have h2 : X * ((β - 1) - (Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) /
          Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)))
          ≤ X * (480 * (N : ℝ) ^ (-(1 / 15 : ℝ))) :=
        mul_le_mul_of_nonneg_left hgapb2 hX0
      have hXnn : (0 : ℝ) ≤ X := hX0
      have hNp : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 / 15 : ℝ)) := Real.rpow_nonneg hN0.le _
      nlinarith [hb1', hb2', h1, h2, hXnn, hNp]
    linarith [hsplit1, hsplit2, hsum]
  -- the lower Riemann bound
  have hGb0 : (0 : ℝ) ≤ G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by
    refine hGnn _ ⟨hkbR, ?_⟩
    push_cast
    linarith
  have hSGlow : J - 960 * X * (N : ℝ) ^ (-(1 / 15 : ℝ))
      ≤ (Real.log (N : ℝ)) ^ 2 *
        (∑ i ∈ Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊ + 1), G (i : ℝ)) := by
    have hL2 : (0 : ℝ) ≤ (Real.log (N : ℝ)) ^ 2 := sq_nonneg _
    have h1 : (Real.log (N : ℝ)) ^ 2 *
        (∫ t in ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)..((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ), G t)
        ≤ (Real.log (N : ℝ)) ^ 2 *
          (∑ i ∈ Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊), G (i : ℝ)) :=
      mul_le_mul_of_nonneg_left hRiem hL2
    have h2 : (Real.log (N : ℝ)) ^ 2 *
        (∑ i ∈ Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊), G (i : ℝ))
        ≤ (Real.log (N : ℝ)) ^ 2 *
          (∑ i ∈ Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊ + 1), G (i : ℝ)) := by
      rw [hsplit]
      have hL2' : (0 : ℝ) ≤ (Real.log (N : ℝ)) ^ 2 := sq_nonneg _
      nlinarith [mul_nonneg hL2' hGb0]
    linarith [h1, h2, hL2subst, hint_ge]
  -- the same sum from above, for the Abel error factor
  have hint_le :
      (∫ s in (Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
          Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))..(Real.log ((N : ℝ) /
            ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) /
            Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)), f s * Kernel616.kernel s)
        ≤ ∫ z in (α - 1)..(β - 1), f z * Kernel616.kernel z := by
    apply intervalIntegral.integral_mono_interval hca hab hbd
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with z hz
      exact mul_nonneg (hfnn z) (kernel_nonneg_of_two (by linarith [hz.1]))
    · exact hInt (α - 1) (β - 1) (by linarith) (by linarith) (by linarith) (by linarith)
  have hconv : ∀ c : ℝ, c * max (f 2) (f 14) / Real.log (N : ℝ) = c * X * (Real.log (N : ℝ))⁻¹ := by
    intro c
    rw [hXdef]
    rw [div_eq_mul_inv]
  have hGk : (Real.log (N : ℝ)) ^ 2 * G ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)
      ≤ 192 * X * (Real.log (N : ℝ))⁻¹ := by
    have h := G_bound hN64 hα hαβ hα15 hβ hβ15 hfmono hfnn
      (t := ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) le_rfl hkbR (by linarith) hlogk
    rw [hconv 192] at h
    exact h
  have hGb : (Real.log (N : ℝ)) ^ 2 * G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)
      ≤ 192 * X * (Real.log (N : ℝ))⁻¹ := by
    have h := G_bound hN64 hα hαβ hα15 hβ hβ15 hfmono hfnn
      (t := ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) hkbR le_rfl (by linarith) hlogb
    rw [hconv 192] at h
    exact h
  have hKGk : (Real.log (N : ℝ)) ^ 2 *
      (((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) * G ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ))
      ≤ 192 * X * (Real.log (N : ℝ))⁻¹ := by
    have h := tG_bound hN64 hα hαβ hα15 hβ hβ15 hfmono hfnn
      (t := ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) le_rfl hkbR (by linarith) hlogk
    rw [hconv 192] at h
    exact h
  have hKGb : (Real.log (N : ℝ)) ^ 2 *
      (((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) * G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))
      ≤ 384 * X * (Real.log (N : ℝ))⁻¹ := by
    have h2b : ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) ≤
        2 * ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by
      have h := upper_cutoff_ge_two hN64 hα hα15
      push_cast
      have h' : (2 : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by exact_mod_cast h
      linarith
    have hbase : (Real.log (N : ℝ)) ^ 2 *
        (((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) * G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))
        ≤ 192 * X * (Real.log (N : ℝ))⁻¹ := by
      have h := tG_bound hN64 hα hαβ hα15 hβ hβ15 hfmono hfnn
        (t := ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) hkbR le_rfl (by linarith) hlogb
      rw [hconv 192] at h
      exact h
    have hL2 : (0 : ℝ) ≤ (Real.log (N : ℝ)) ^ 2 := sq_nonneg _
    calc (Real.log (N : ℝ)) ^ 2 *
          (((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) * G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))
        ≤ (Real.log (N : ℝ)) ^ 2 *
            (2 * (((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) * G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hL2
          have h1 : ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) * G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)
              ≤ (2 * ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) * G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right h2b hGb0
          have h2' : (2 * ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) *
              G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)
              = 2 * (((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) *
                G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) := by ring
          linarith
      _ = 2 * ((Real.log (N : ℝ)) ^ 2 *
            (((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) * G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))) := by ring
      _ ≤ 2 * (192 * X * (Real.log (N : ℝ))⁻¹) := by linarith
      _ = 384 * X * (Real.log (N : ℝ))⁻¹ := by ring
  have hS : (Real.log (N : ℝ)) ^ 2 *
      (∑ i ∈ Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊ + 1), G (i : ℝ))
      ≤ J + 384 * X * (Real.log (N : ℝ))⁻¹ := by
    have hR : (Real.log (N : ℝ)) ^ 2 *
        (∑ i ∈ Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊), G (i : ℝ))
        ≤ J + (Real.log (N : ℝ)) ^ 2 * G ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by
      have hupper : (∑ i ∈ Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊), G (i : ℝ))
          ≤ (∫ t in ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)..((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ), G t)
            + G ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by
        refine sum_Ico_le_integral_add hkb hantiOn ?_
        intro t ht
        exact G_nonneg hN64 hα hβ hβ15 hfnn ht.1 (by
          have : ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) := by
            push_cast; linarith
          linarith [ht.2])
      have h := mul_le_mul_of_nonneg_left hupper (sq_nonneg (Real.log (N : ℝ)))
      calc (Real.log (N : ℝ)) ^ 2 *
            (∑ i ∈ Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊), G (i : ℝ))
          ≤ (Real.log (N : ℝ)) ^ 2 *
              ((∫ t in ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)..((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ), G t)
                + G ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) := h
        _ = (Real.log (N : ℝ)) ^ 2 *
              (∫ t in ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)..((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ), G t)
            + (Real.log (N : ℝ)) ^ 2 * G ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by ring
        _ ≤ J + (Real.log (N : ℝ)) ^ 2 * G ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by
          have hh := hL2subst
          linarith [hint_le, hh]
    have hdist2 : (Real.log (N : ℝ)) ^ 2 *
        ((∑ i ∈ Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊), G (i : ℝ))
          + G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ))
        = (Real.log (N : ℝ)) ^ 2 *
            (∑ i ∈ Finset.Ico (⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (⌊(N : ℝ) ^ (1 / α)⌋₊), G (i : ℝ))
          + (Real.log (N : ℝ)) ^ 2 * G ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by ring
    have hsum384 : 192 * X * (Real.log (N : ℝ))⁻¹ + 192 * X * (Real.log (N : ℝ))⁻¹
        = 384 * X * (Real.log (N : ℝ))⁻¹ := by ring
    rw [hsplit]
    linarith [hdist2, hR, hGb, hsum384]
  have hXL : (0 : ℝ) ≤ X * (Real.log (N : ℝ))⁻¹ := by positivity
  have hL2sq : (0 : ℝ) ≤ (Real.log (N : ℝ)) ^ 2 := sq_nonneg _
  rw [hband]
  exact eps_assembly_ge hAbel hKGk hKGb hS hSGlow hε0 hε64 hXL hL2sq

/-- At most fifteen primes above `N^(1/15)` divide `N`: their product divides `N`. -/
private theorem bad_primes_card_le {N : ℕ} (hN : 2 ≤ N) {S : Finset ℕ}
    (hprime : ∀ p ∈ S, p.Prime) (hdvd : ∀ p ∈ S, p ∣ N)
    (hge : ∀ p ∈ S, (N : ℝ) ^ ((1 : ℝ) / 15) ≤ (p : ℝ)) :
    S.card ≤ 15 := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    have : (1 : ℕ) < N := by omega
    exact_mod_cast this
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hsub : S ⊆ N.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hprime p hp, hdvd p hp, by omega⟩
  have hprod_dvd : (∏ p ∈ S, p) ∣ N := by
    refine dvd_trans ?_ (Nat.prod_primeFactors_dvd N)
    exact Finset.prod_dvd_prod_of_subset S N.primeFactors (fun p => p) hsub
  have hprod_le : (∏ p ∈ S, (p : ℝ)) ≤ (N : ℝ) := by
    have h := Nat.le_of_dvd (by omega : 0 < N) hprod_dvd
    have h' : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
    simpa using h'
  have hposS : ∀ p ∈ S, (0 : ℝ) < (p : ℝ) := fun p hp => by
    exact_mod_cast (hprime p hp).pos
  have hlog_le : ∑ p ∈ S, Real.log (p : ℝ) ≤ Real.log (N : ℝ) := by
    have hlogprod : Real.log (∏ p ∈ S, (p : ℝ)) = ∑ p ∈ S, Real.log (p : ℝ) :=
      Real.log_prod (s := S) (f := fun p : ℕ => (p : ℝ)) (fun p hp => (hposS p hp).ne')
    rw [← hlogprod]
    exact Real.log_le_log (Finset.prod_pos hposS) hprod_le
  have heach : ∀ p ∈ S, Real.log (N : ℝ) / 15 ≤ Real.log (p : ℝ) := by
    intro p hp
    have h1 := Real.log_le_log (by positivity) (hge p hp)
    rw [Real.log_rpow hN0] at h1
    calc Real.log (N : ℝ) / 15 = 1 / 15 * Real.log (N : ℝ) := by ring
      _ ≤ Real.log (p : ℝ) := h1
  have hcard : (S.card : ℝ) * (Real.log (N : ℝ) / 15) ≤ Real.log (N : ℝ) := by
    have h := Finset.sum_le_sum heach
    rw [Finset.sum_const, nsmul_eq_mul] at h
    linarith
  have hfin : (S.card : ℝ) ≤ 15 := by
    have hpos : (0 : ℝ) < Real.log (N : ℝ) / 15 := by positivity
    nlinarith [hcard, hL]
  exact_mod_cast hfin

/-- `C * N^(-1/15)` is eventually below any positive constant. -/
private theorem eventually_rpow_neg_le {C c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, C * (N : ℝ) ^ (-(1 / 15 : ℝ)) ≤ c := by
  have h0 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 / 15 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (y := 1 / 15) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-(1 / 15 : ℝ))) atTop (nhds (C * 0)) :=
    h0.const_mul C
  have h2 : Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-(1 / 15 : ℝ))) atTop (nhds 0) := by
    simpa using h1
  exact h2.eventually (eventually_le_nhds hc)

/-- For `α < β` the prime band is eventually nonempty. -/
private theorem band_eventually_nonempty {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hlt : α < β) :
    ∀ᶠ N : ℕ in atTop, ⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 < ⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 := by
  have hs : 0 < (1 : ℝ) / α - 1 / β := by
    have h : (1 : ℝ) / β < 1 / α := one_div_lt_one_div_of_lt hα hlt
    linarith
  have hpow : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / α - 1 / β) :=
    ((tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 2)
  have hx4 : ∀ᶠ N : ℕ in atTop, (4 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / α) :=
    ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < 1 / α)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 4)
  filter_upwards [hpow, hx4, eventually_ge_atTop 1] with N h1 h2 h3
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℕ) < N := by omega
    exact_mod_cast this
  have hy0 : (0 : ℝ) < (N : ℝ) ^ (1 / β) := Real.rpow_pos_of_pos hN0 _
  have hsplit : (N : ℝ) ^ ((1 : ℝ) / α) = (N : ℝ) ^ (1 / β) * (N : ℝ) ^ ((1 : ℝ) / α - 1 / β) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  have hdiff : (N : ℝ) ^ (1 / β) + 2 ≤ (N : ℝ) ^ ((1 : ℝ) / α) := by
    rw [hsplit]
    nlinarith [h1, hy0]
  have hfloor : ((⌊(N : ℝ) ^ (1 / β)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / β) := Nat.floor_le (le_of_lt hy0)
  have hfloorx : (N : ℝ) ^ ((1 : ℝ) / α) - 1 < ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one ((N : ℝ) ^ ((1 : ℝ) / α))
    push_cast
    linarith
  have hkey : ((⌊(N : ℝ) ^ (1 / β)⌋₊ : ℕ) : ℝ) + 1 ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by
    linarith
  have hnat : ⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 ≤ ⌊(N : ℝ) ^ (1 / α)⌋₊ := by exact_mod_cast hkey
  omega
set_option maxHeartbeats 2000000 in
/-- LEAF Buchstab1938 pp. 382 to 383, display 7 and its upper integral estimate.
The uniform auxiliary quotient bound is explicit. P0072 uses the extended range through fifteen.
OPEN sum to integral transfer. A bound on the original P0072 count alone is insufficient. -/
theorem upper_removed_transfer (T α β : ℝ) (hT : 0 < T)
    (hα : 3 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 15)
    (U : ℝ → ℝ) (hU : Monotone U) (hU0 : ∀ z ∈ Set.Icc 2 14, 0 ≤ U z)
    (haux : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      ∀ p : ℕ, p.Prime → p.Coprime N → cutoff N β ≤ (p : ℝ) → (p : ℝ) < cutoff N α →
      childMass N p ≤ 2 * (U (log ((N : ℝ) / p) / log p) + δ) *
        M T N * (log N) ^ 2 / ((p : ℝ) * (log ((N : ℝ) / p)) ^ 2)) :
    ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, Even N →
      (Finite616.removed N (cutoff N β) (cutoff N α)).re ≤
        (2 * (∫ z in (α - 1)..(β - 1), U z * Kernel616.kernel z) + η) * M T N := by
  intro η hη
  have hβ0 : 0 < β := lt_of_lt_of_le (by norm_num) (le_trans hα hαβ)
  have hα15 : α ≤ 15 := le_trans hαβ hβ
  set J : ℝ := ∫ z in (α - 1)..(β - 1), U z * Kernel616.kernel z with hJdef
  set J1 : ℝ := ∫ z in (α - 1)..(β - 1), Kernel616.kernel z with hJ1def
  set X : ℝ := max (U 2) (U 14) with hXdef
  have hXnn : 0 ≤ X := le_trans (hU0 14 ⟨by norm_num, le_rfl⟩) (le_max_right _ _)
  have hJnn : 0 ≤ J := by
    rw [hJdef]
    refine intervalIntegral.integral_nonneg (by linarith) ?_
    intro z hz
    exact mul_nonneg (hU0 z ⟨by linarith [hz.1], by linarith [hz.2]⟩)
      (kernel_nonneg_of_two (by linarith [hz.1]))
  have hJ1nn : 0 ≤ J1 := by
    rw [hJ1def]
    refine intervalIntegral.integral_nonneg (by linarith) ?_
    intro z hz
    exact kernel_nonneg_of_two (by linarith [hz.1])
  set δ : ℝ := η / (256 * (J1 + 1)) with hδdef
  have hδ0 : 0 < δ := by
    rw [hδdef]
    have : (0 : ℝ) < 256 * (J1 + 1) := by linarith
    positivity
  set ε : ℝ := min (1 / 64) (η / (128 * (J + 1))) with hεdef
  have hε0 : 0 < ε := by
    rw [hεdef]
    exact lt_min (by norm_num) (by positivity)
  have hε64 : ε ≤ 1 / 64 := min_le_left _ _
  have hεsmall : ε ≤ η / (128 * (J + 1)) := min_le_right _ _
  -- the three elementary budget inequalities
  have hb1 : 2 * (δ * J1) ≤ η / 8 := by
    have hpos : (0 : ℝ) < J1 + 1 := by linarith
    have hdJ : δ * J1 ≤ η / 16 := by
      rw [hδdef]
      rw [show η / (256 * (J1 + 1)) * J1 = η * J1 / (256 * (J1 + 1)) by ring]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 256 * (J1 + 1))]
      nlinarith [hη, hJ1nn]
    linarith
  have hb2 : 8 * ε * J ≤ η / 8 := by
    have hpos : (0 : ℝ) < J + 1 := by linarith
    have hJle : J / (J + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have hstep : ε * J ≤ (η / (128 * (J + 1))) * J := mul_le_mul_of_nonneg_right hεsmall hJnn
    have hrw : (η / (128 * (J + 1))) * J = η / 128 * (J / (J + 1)) := by
      field_simp
    rw [hrw] at hstep
    nlinarith [hstep, hJle, hη]
  have hb3 : 8 * ε * (δ * J1) ≤ η / 16 := by
    have hpos : (0 : ℝ) < J1 + 1 := by linarith
    have hδJ1 : δ * J1 ≤ η / 256 := by
      rw [hδdef]
      rw [show η / (256 * (J1 + 1)) * J1 = η * J1 / (256 * (J1 + 1)) by ring]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 256 * (J1 + 1))]
      nlinarith [hJ1nn, hη]
    have hδJ1nn : 0 ≤ δ * J1 := by
      have : 0 ≤ δ := le_of_lt hδ0
      exact mul_nonneg this hJ1nn
    have hεle : ε ≤ 1 / 64 := hε64
    nlinarith [hδJ1, hδJ1nn, hεle, hε0, hη]
  -- the analytic bound on the band sum
  have hθev := theta_uniform_error hε0
  have hauxδ := haux δ hδ0
  have hsize := section5_size_inputs hT (by norm_num : (0 : ℝ) < 1)
  filter_upwards [eventually_ge_atTop (2 ^ 240 : ℕ), eventually_ge_atTop 65536, hθev, hauxδ,
    hsize, eventually_log_ge (max 167 (max (4000 * X / η) (16 * (J1 + 1)⁻¹)))] with N hNbig hN64 hθN hauxN hsizeN hLge
  intro hEven
  have hNterm : (2 : ℝ) ^ (240 : ℝ) ≤ (N : ℝ) := by
    have heq : (2 : ℝ) ^ (240 : ℝ) = ((2 ^ 240 : ℕ) : ℝ) := by
      rw [show (240 : ℝ) = ((240 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
      norm_num
    rw [heq]
    exact_mod_cast hNbig
  have hL167 : (167 : ℝ) ≤ Real.log (N : ℝ) :=
    le_trans (le_max_left (167 : ℝ) (max (4000 * X / η) (16 * (J1 + 1)⁻¹))) hLge
  have hL4000 : 4000 * X / η ≤ Real.log (N : ℝ) :=
    le_trans (le_max_left (4000 * X / η) (16 * (J1 + 1)⁻¹))
      (le_trans (le_max_right (167 : ℝ) (max (4000 * X / η) (16 * (J1 + 1)⁻¹))) hLge)
  have hL16 : 16 * (J1 + 1)⁻¹ ≤ Real.log (N : ℝ) :=
    le_trans (le_max_right (4000 * X / η) (16 * (J1 + 1)⁻¹))
      (le_trans (le_max_right (167 : ℝ) (max (4000 * X / η) (16 * (J1 + 1)⁻¹))) hLge)
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    have : (1 : ℕ) < N := by omega
    exact_mod_cast this
  have hLpos : (0 : ℝ) < Real.log (N : ℝ) := Real.log_pos hN1
  have hbNlt : ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) < (N : ℝ) := upper_cutoff_lt hN64 hα
  have hM0 : 0 < M T N := by linarith [hsizeN.2]
  have hMnn : 0 ≤ M T N := le_of_lt hM0
  -- monotone nonnegative weight
  set F : ℝ → ℝ := fun z => max (U z) 0 + δ with hFdef
  have hFmono : Monotone F := by
    intro a b hab
    have h1 : max (U a) (0 : ℝ) ≤ max (U b) (0 : ℝ) := max_le_max (hU hab) le_rfl
    have h2 : max (U a) (0 : ℝ) + δ ≤ max (U b) (0 : ℝ) + δ := by linarith
    exact h2
  have hFnn : ∀ z, 0 ≤ F z := by
    intro z
    have : (0 : ℝ) ≤ max (U z) 0 := le_max_right _ _
    linarith
  have hanalytic := char_sum_le hNterm hα hαβ hα15 hβ0 hβ hFmono hFnn (le_of_lt hε0) hε64 hθN
    (log_lower_cutoff_ge (by omega : 1 ≤ N) hβ0 hβ)
    (log_upper_cutoff_ge hN64 hα hα15 hL167)
  -- identify the two sides of that bound
  have hFint : ∀ᵉ (z : ℝ), z ∈ Set.uIcc (α - 1) (β - 1) → F z = U z + δ := by
    intro z hz
    have hz1 : (2 : ℝ) ≤ z := by
      rw [Set.uIcc_of_le (by linarith : α - 1 ≤ β - 1)] at hz
      linarith [hz.1]
    have hz2 : z ≤ 14 := by
      rw [Set.uIcc_of_le (by linarith : α - 1 ≤ β - 1)] at hz
      linarith [hz.2]
    show max (U z) 0 + δ = U z + δ
    rw [max_eq_left (hU0 z ⟨hz1, hz2⟩)]
  have hint : (∫ z in (α - 1)..(β - 1), F z * Kernel616.kernel z) = J + δ * J1 := by
    have hcongr : (∫ z in (α - 1)..(β - 1), F z * Kernel616.kernel z)
        = ∫ z in (α - 1)..(β - 1), (U z + δ) * Kernel616.kernel z := by
      apply intervalIntegral.integral_congr
      intro z hz
      show F z * Kernel616.kernel z = (U z + δ) * Kernel616.kernel z
      rw [hFint z hz]
    have hsplit : (∫ z in (α - 1)..(β - 1), (U z + δ) * Kernel616.kernel z)
        = (∫ z in (α - 1)..(β - 1), U z * Kernel616.kernel z)
          + ∫ z in (α - 1)..(β - 1), δ * Kernel616.kernel z := by
      have h1 : IntervalIntegrable (fun z => U z * Kernel616.kernel z) MeasureTheory.volume (α - 1) (β - 1) :=
        intervalIntegrable_mul_kernel (by linarith : (2 : ℝ) ≤ α - 1) (by linarith : α - 1 ≤ 14)
          (by linarith : (2 : ℝ) ≤ β - 1) (by linarith : β - 1 ≤ 14) hU hU0
      have h2 : IntervalIntegrable (fun z => δ * Kernel616.kernel z) MeasureTheory.volume (α - 1) (β - 1) :=
        intervalIntegrable_mul_kernel (by linarith : (2 : ℝ) ≤ α - 1) (by linarith : α - 1 ≤ 14)
          (by linarith : (2 : ℝ) ≤ β - 1) (by linarith : β - 1 ≤ 14) monotone_const
          (fun z _ => le_of_lt hδ0)
      rw [← intervalIntegral.integral_add h1 h2]
      apply intervalIntegral.integral_congr
      intro z hz
      ring
    have hconst : (∫ z in (α - 1)..(β - 1), δ * Kernel616.kernel z)
        = δ * J1 := by
      rw [hJ1def, intervalIntegral.integral_const_mul]
    rw [hcongr, hsplit, hconst, hJdef]
  have hmaxF : max (F 2) (F 14) ≤ X + δ := by
    have h2 : F 2 = U 2 + δ := by
      show max (U 2) 0 + δ = U 2 + δ
      rw [max_eq_left (hU0 2 ⟨le_rfl, by norm_num⟩)]
    have h14 : F 14 = U 14 + δ := by
      show max (U 14) 0 + δ = U 14 + δ
      rw [max_eq_left (hU0 14 ⟨by norm_num, le_rfl⟩)]
    rw [h2, h14]
    exact max_le (by linarith [le_max_left (U 2) (U 14)])
      (by linarith [le_max_right (U 2) (U 14)])
  -- bound the removed mass by the band sum
  have hrem : (Finite616.removed N (cutoff N β) (cutoff N α)).re
      ≤ 2 * M T N * (Real.log (N : ℝ)) ^ 2 *
        (∑ p ∈ primeBand N (cutoff N β) (cutoff N α),
          (U (Real.log ((N : ℝ) / p) / Real.log p) + δ) *
            (1 / ((p : ℝ) * (Real.log ((N : ℝ) / p)) ^ 2))) := by
    rw [removed_eq_sum_coprime (by omega : 1 < N)]
    have hstep1 : (∑ p ∈ (primeBand N (cutoff N β) (cutoff N α)).filter
          (fun p => p.Coprime N), childMass N p)
        ≤ ∑ p ∈ (primeBand N (cutoff N β) (cutoff N α)).filter (fun p => p.Coprime N),
            2 * (U (Real.log ((N : ℝ) / p) / Real.log p) + δ) * M T N *
              (Real.log (N : ℝ)) ^ 2 / ((p : ℝ) * (Real.log ((N : ℝ) / p)) ^ 2) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpband, hpcop⟩ := Finset.mem_filter.mp hp
      obtain ⟨-, hpprime, hw, hz⟩ := Finset.mem_filter.mp hpband
      exact hauxN hEven p hpprime hpcop hw hz
    have hstep2 : (∑ p ∈ (primeBand N (cutoff N β) (cutoff N α)).filter (fun p => p.Coprime N),
          2 * (U (Real.log ((N : ℝ) / p) / Real.log p) + δ) * M T N *
            (Real.log (N : ℝ)) ^ 2 / ((p : ℝ) * (Real.log ((N : ℝ) / p)) ^ 2))
        ≤ ∑ p ∈ primeBand N (cutoff N β) (cutoff N α),
            2 * (U (Real.log ((N : ℝ) / p) / Real.log p) + δ) * M T N *
              (Real.log (N : ℝ)) ^ 2 / ((p : ℝ) * (Real.log ((N : ℝ) / p)) ^ 2) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro p hp _
      obtain ⟨-, hpprime, hw, hz⟩ := Finset.mem_filter.mp hp
      have htk : ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
        rw [cutoff_eq_coe_succ] at hw
        exact hw
      have htm : (p : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by
        have hpcut : p < ⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 := by
          rw [cutoff_eq_coe_succ] at hz
          exact_mod_cast hz
        have : p ≤ ⌊(N : ℝ) ^ (1 / α)⌋₊ := by omega
        exact_mod_cast this
      obtain ⟨hφ2, hφ14⟩ := phi_mem hN64 hα hαβ hβ0 hβ hα15 htk htm
      have hUφ : (0 : ℝ) ≤ U (Real.log ((N : ℝ) / p) / Real.log p) := hU0 _ ⟨hφ2, hφ14⟩
      have hterm : (0 : ℝ) ≤ 2 * (U (Real.log ((N : ℝ) / p) / Real.log p) + δ) * M T N *
          (Real.log (N : ℝ)) ^ 2 / ((p : ℝ) * (Real.log ((N : ℝ) / p)) ^ 2) := by
        have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpprime.pos
        have hlogp : (0 : ℝ) < Real.log ((N : ℝ) / p) := by
          apply Real.log_pos
          rw [one_lt_div hp0]
          have hpN : (p : ℝ) < (N : ℝ) := lt_of_le_of_lt htm hbNlt
          linarith
        have hden : (0 : ℝ) < (p : ℝ) * (Real.log ((N : ℝ) / p)) ^ 2 := by positivity
        have hnum : (0 : ℝ) ≤ 2 * (U (Real.log ((N : ℝ) / p) / Real.log p) + δ) * M T N *
            (Real.log (N : ℝ)) ^ 2 := by
          have h1 : (0 : ℝ) ≤ U (Real.log ((N : ℝ) / p) / Real.log p) + δ := by linarith
          have h2 : (0 : ℝ) ≤ (Real.log (N : ℝ)) ^ 2 := sq_nonneg _
          have h3 : (0 : ℝ) ≤ 2 * (U (Real.log ((N : ℝ) / p) / Real.log p) + δ) := by linarith
          exact mul_nonneg (mul_nonneg h3 hMnn) h2
        exact div_nonneg hnum (le_of_lt hden)
      exact hterm
    have hstep3 : (∑ p ∈ primeBand N (cutoff N β) (cutoff N α),
          2 * (U (Real.log ((N : ℝ) / p) / Real.log p) + δ) * M T N *
            (Real.log (N : ℝ)) ^ 2 / ((p : ℝ) * (Real.log ((N : ℝ) / p)) ^ 2))
        = 2 * M T N * (Real.log (N : ℝ)) ^ 2 *
          (∑ p ∈ primeBand N (cutoff N β) (cutoff N α),
            (U (Real.log ((N : ℝ) / p) / Real.log p) + δ) *
              (1 / ((p : ℝ) * (Real.log ((N : ℝ) / p)) ^ 2))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    linarith [hstep1, hstep2, hstep3]
  -- identify the weight sum with the one bounded analytically
  have hsumEq : (∑ p ∈ primeBand N (cutoff N β) (cutoff N α),
        F (Real.log ((N : ℝ) / p) / Real.log p) *
          (1 / ((p : ℝ) * (Real.log ((N : ℝ) / p)) ^ 2)))
      = ∑ p ∈ primeBand N (cutoff N β) (cutoff N α),
          (U (Real.log ((N : ℝ) / p) / Real.log p) + δ) *
            (1 / ((p : ℝ) * (Real.log ((N : ℝ) / p)) ^ 2)) := by
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨-, hpprime, hw, hz⟩ := Finset.mem_filter.mp hp
    have htk : ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
      rw [cutoff_eq_coe_succ] at hw
      exact hw
    have htm : (p : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by
      have hpcut : p < ⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 := by
        rw [cutoff_eq_coe_succ] at hz
        exact_mod_cast hz
      have : p ≤ ⌊(N : ℝ) ^ (1 / α)⌋₊ := by omega
      exact_mod_cast this
    obtain ⟨hφ2, hφ14⟩ := phi_mem hN64 hα hαβ hβ0 hβ hα15 htk htm
    have hUφ : (0 : ℝ) ≤ U (Real.log ((N : ℝ) / p) / Real.log p) := hU0 _ ⟨hφ2, hφ14⟩
    show (max (U (Real.log ((N : ℝ) / p) / Real.log p)) 0 + δ) *
        (1 / ((p : ℝ) * (Real.log ((N : ℝ) / p)) ^ 2))
      = (U (Real.log ((N : ℝ) / p) / Real.log p) + δ) *
        (1 / ((p : ℝ) * (Real.log ((N : ℝ) / p)) ^ 2))
    rw [max_eq_left hUφ]
  -- the budget
  have h4 : 1000 * X / Real.log (N : ℝ) ≤ η / 4 := by
    rw [div_le_iff₀ hLpos]
    have h := mul_le_mul_of_nonneg_left hL4000 (le_of_lt hη)
    have heq : η * (4000 * X / η) = 4000 * X := by field_simp
    rw [heq] at h
    nlinarith [h]
  have h5 : 1000 * δ / Real.log (N : ℝ) ≤ η / 4 := by
    have hpos : (0 : ℝ) < J1 + 1 := by linarith
    have h16 := mul_le_mul_of_nonneg_left hL16 (by positivity : (0 : ℝ) ≤ η / 4)
    have heq : (η / 4) * (16 * (J1 + 1)⁻¹) = 4 * η / (J1 + 1) := by
      field_simp
      norm_num
    rw [heq] at h16
    have hd1 : 1000 * δ ≤ 4 * η / (J1 + 1) := by
      rw [hδdef]
      rw [show 1000 * (η / (256 * (J1 + 1))) = 1000 * η / (256 * (J1 + 1)) by ring]
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 256 * (J1 + 1)) hpos]
      nlinarith [hη, hpos]
    rw [div_le_iff₀ hLpos]
    linarith [hd1, h16]
  have hbudget : 2 * (δ * J1 + 4 * ε * (J + δ * J1) + 500 * (X + δ) / Real.log (N : ℝ)) ≤ η := by
    have hexp : 2 * (δ * J1 + 4 * ε * (J + δ * J1) + 500 * (X + δ) / Real.log (N : ℝ))
        = 2 * (δ * J1) + 8 * ε * J + 8 * ε * (δ * J1) + 1000 * X / Real.log (N : ℝ)
          + 1000 * δ / Real.log (N : ℝ) := by
      ring_nf
    rw [hexp]
    linarith [hb1, hb2, hb3, h4, h5]
  have hSbound : (Real.log (N : ℝ)) ^ 2 *
      (∑ p ∈ primeBand N (cutoff N β) (cutoff N α),
        (U (Real.log ((N : ℝ) / p) / Real.log p) + δ) *
          (1 / ((p : ℝ) * (Real.log ((N : ℝ) / p)) ^ 2)))
      ≤ J + δ * J1 + 4 * ε * (J + δ * J1) + 500 * (X + δ) / Real.log (N : ℝ) := by
    have h := hanalytic
    rw [hsumEq, hint] at h
    have h500 : 500 * max (F 2) (F 14) / Real.log (N : ℝ) ≤
        500 * (X + δ) / Real.log (N : ℝ) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hLpos)
      linarith [hmaxF]
    linarith [h, h500]
  have hstepM : 2 * M T N * ((Real.log (N : ℝ)) ^ 2 *
      (∑ p ∈ primeBand N (cutoff N β) (cutoff N α),
        (U (Real.log ((N : ℝ) / p) / Real.log p) + δ) *
          (1 / ((p : ℝ) * (Real.log ((N : ℝ) / p)) ^ 2))))
      ≤ 2 * M T N * (J + δ * J1 + 4 * ε * (J + δ * J1) + 500 * (X + δ) / Real.log (N : ℝ)) :=
    mul_le_mul_of_nonneg_left hSbound (by linarith : (0 : ℝ) ≤ 2 * M T N)
  rw [hJdef]
  nlinarith [hrem, hstepM, hbudget, hMnn, hη]

set_option maxHeartbeats 8000000 in
/-- LEAF Buchstab1938 p. 383 Theorem 2, the mirror lower integral estimate.
The uniform auxiliary lower bound and the range extension are retained explicitly.
OPEN sum to integral transfer. -/
theorem lower_removed_transfer (T α β : ℝ) (hT : 0 < T)
    (hα : 3 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 15)
    (L : ℝ → ℝ) (hL : Monotone L) (hL0 : ∀ z ∈ Set.Icc 2 14, 0 ≤ L z)
    (haux : ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop, Even N →
      ∀ p : ℕ, p.Prime → p.Coprime N → cutoff N β ≤ (p : ℝ) → (p : ℝ) < cutoff N α →
      2 * (L (log ((N : ℝ) / p) / log p) - δ) *
        M T N * (log N) ^ 2 / ((p : ℝ) * (log ((N : ℝ) / p)) ^ 2) ≤ childMass N p) :
    ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, Even N →
      (2 * (∫ z in (α - 1)..(β - 1), L z * Kernel616.kernel z) - η) * M T N ≤
        (Finite616.removed N (cutoff N β) (cutoff N α)).re := by
  intro η hη
  rcases eq_or_lt_of_le hαβ with rfl | hαlt
  · -- equal exponents: the band is empty and the integral vanishes
    filter_upwards [section5_size_inputs hT (by norm_num : (0 : ℝ) < 1),
      eventually_ge_atTop 2] with N hsize hN2
    intro hEven
    have hM0 : 0 < M T N := by linarith [hsize.2]
    have hJ : (∫ z in (α - 1)..(α - 1), L z * Kernel616.kernel z) = 0 := by simp
    rw [hJ]
    have hnonneg : (0 : ℝ) ≤ (Finite616.removed N (cutoff N α) (cutoff N α)).re := by
      rw [removed_eq_sum_coprime (N := N) (by omega : 1 < N) (cutoff N α) (cutoff N α)]
      exact Finset.sum_nonneg (fun p hp => childMass_nonneg N p)
    nlinarith
  · -- strict: the band is eventually nonempty
    have hα0 : 0 < α := by linarith
    have hβ0 : 0 < β := lt_of_le_of_lt (by linarith) hαlt
    have hα15 : α ≤ 15 := le_trans hαβ hβ
    set F : ℝ → ℝ := fun z => max (L z) 0 with hFdef
    have hFmono : Monotone F := fun a b hab => max_le_max (hL hab) le_rfl
    have hFnn : ∀ z, 0 ≤ F z := fun z => le_max_right _ _
    set J : ℝ := ∫ z in (α - 1)..(β - 1), L z * Kernel616.kernel z with hJdef
    set J1 : ℝ := ∫ z in (α - 1)..(β - 1), Kernel616.kernel z with hJ1def
    set X : ℝ := max (F 2) (F 14) with hXdef
    have hXnn : 0 ≤ X := le_trans (hFnn 14) (le_max_right _ _)
    have hJnn : 0 ≤ J := by
      rw [hJdef]
      refine intervalIntegral.integral_nonneg (by linarith) ?_
      intro z hz
      exact mul_nonneg (hL0 z ⟨by linarith [hz.1], by linarith [hz.2]⟩)
        (kernel_nonneg_of_two (by linarith [hz.1]))
    have hJ1nn : 0 ≤ J1 := by
      rw [hJ1def]
      refine intervalIntegral.integral_nonneg (by linarith) ?_
      intro z hz
      exact kernel_nonneg_of_two (by linarith [hz.1])
    set δ : ℝ := η / (1024 * (J1 + 1)) with hδdef
    have hδ0 : 0 < δ := by
      rw [hδdef]
      have : (0 : ℝ) < 1024 * (J1 + 1) := by linarith
      positivity
    set ε : ℝ := min (1 / 64) (η / (128 * (J + 1))) with hεdef
    have hε0 : 0 < ε := by
      rw [hεdef]
      exact lt_min (by norm_num) (by positivity)
    have hε64 : ε ≤ 1 / 64 := min_le_left _ _
    have hεsmall : ε ≤ η / (128 * (J + 1)) := min_le_right _ _
    have hb1 : 8 * ε * J ≤ η / 8 := by
      have hpos : (0 : ℝ) < J + 1 := by linarith
      have hJle : J / (J + 1) ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      have hstep : ε * J ≤ (η / (128 * (J + 1))) * J := mul_le_mul_of_nonneg_right hεsmall hJnn
      have hrw : (η / (128 * (J + 1))) * J = η / 128 * (J / (J + 1)) := by
        field_simp <;> ring
      rw [hrw] at hstep
      nlinarith [hstep, hJle, hη]
    have hb2 : 2 * (δ * J1) ≤ η / 8 := by
      have hpos : (0 : ℝ) < J1 + 1 := by linarith
      have hdJ : δ * J1 ≤ η / 16 := by
        rw [hδdef]
        rw [show η / (1024 * (J1 + 1)) * J1 = η * J1 / (1024 * (J1 + 1)) by ring]
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1024 * (J1 + 1))]
        nlinarith [hη, hJ1nn]
      linarith
    have hb3 : 8 * ε * (δ * J1) ≤ η / 8 := by
      have hpos : (0 : ℝ) < J1 + 1 := by linarith
      have hδJ1 : δ * J1 ≤ η / 1024 := by
        rw [hδdef]
        rw [show η / (1024 * (J1 + 1)) * J1 = η * J1 / (1024 * (J1 + 1)) by ring]
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1024 * (J1 + 1))]
        nlinarith [hJ1nn, hη]
      have hδJ1nn : 0 ≤ δ * J1 := mul_nonneg (le_of_lt hδ0) hJ1nn
      nlinarith [hδJ1, hδJ1nn, hε64, hε0, hη]
    have hθev := theta_uniform_error hε0
    have hauxδ := haux δ hδ0
    have hsize := section5_size_inputs hT (by norm_num : (0 : ℝ) < 1)
    have hne := band_eventually_nonempty hα0 hαβ hαlt
    have hrpow := eventually_rpow_neg_le (C := 2000 * X) (c := η / 8) (by positivity)
    filter_upwards [eventually_ge_atTop (2 ^ 240 : ℕ), eventually_ge_atTop 65536, hθev, hauxδ,
      hsize, hne, hrpow,
      eventually_log_ge (max 167 (max (16000 * X / η) (16 * (J1 + 1)⁻¹)))] with N hNbig hN64 hθN hauxN
      hsizeN hltN hrpowN hLge
    intro hEven
    have hNterm : (2 : ℝ) ^ (240 : ℝ) ≤ (N : ℝ) := by
      have heq : (2 : ℝ) ^ (240 : ℝ) = ((2 ^ 240 : ℕ) : ℝ) := by
        rw [show (240 : ℝ) = ((240 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
        norm_num
      rw [heq]
      exact_mod_cast hNbig
    have hN0 : (0 : ℝ) < (N : ℝ) := by
      have : (0 : ℕ) < N := by omega
      exact_mod_cast this
    have hN1 : (1 : ℝ) < (N : ℝ) := by
      have : (1 : ℕ) < N := by omega
      exact_mod_cast this
    have hL : (0 : ℝ) < Real.log (N : ℝ) := Real.log_pos hN1
    have hL167 : (167 : ℝ) ≤ Real.log (N : ℝ) :=
      le_trans (le_max_left (167 : ℝ) (max (16000 * X / η) (16 * (J1 + 1)⁻¹))) hLge
    have hL4000 : 16000 * X / η ≤ Real.log (N : ℝ) :=
      le_trans (le_max_left (16000 * X / η) (16 * (J1 + 1)⁻¹))
        (le_trans (le_max_right (167 : ℝ) (max (16000 * X / η) (16 * (J1 + 1)⁻¹))) hLge)
    have hL16 : 16 * (J1 + 1)⁻¹ ≤ Real.log (N : ℝ) :=
      le_trans (le_max_right (16000 * X / η) (16 * (J1 + 1)⁻¹))
        (le_trans (le_max_right (167 : ℝ) (max (16000 * X / η) (16 * (J1 + 1)⁻¹))) hLge)
    have hM0 : 0 < M T N := by linarith [hsizeN.2]
    have hMnn : 0 ≤ M T N := le_of_lt hM0
    have hbNlt : ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) < (N : ℝ) := upper_cutoff_lt hN64 hα
    have hble : ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / α) := Nat.floor_le (by positivity)
    have hb1' : (1 : ℝ) < ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by
      have h2 := upper_cutoff_ge_two hN64 hα hα15
      have h2' : (2 : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by exact_mod_cast h2
      linarith
    have hk3 : 3 ≤ ⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 := lower_cutoff_ge_three hN64 hβ0 hβ
    have hk1 : (1 : ℝ) < ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by
      have h : (3 : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hk3
      linarith
    have hkN : ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) < (N : ℝ) := by
      have hm8 : ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) ≤ (N : ℝ) / 8 :=
        upper_cutoff_le (by omega : 64 ≤ N) (hα.trans hαβ)
      have hN8 : (0 : ℝ) < (N : ℝ) / 8 := by linarith
      linarith
    have hkge : (N : ℝ) ^ (1 / β) ≤ ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by
      have h := Nat.lt_floor_add_one ((N : ℝ) ^ (1 / β))
      push_cast
      linarith
    have hca : α - 1 ≤ Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ)) /
        Real.log ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) :=
      le_phi_upper_cutoff (N := (N : ℝ)) (α := α) hN1 (by linarith) (by linarith)
        (b := ⌊(N : ℝ) ^ (1 / α)⌋₊) (by omega) hbNlt hble
    have hbd : Real.log ((N : ℝ) / ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ)) /
        Real.log ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) ≤ β - 1 :=
      phi_lower_cutoff_le (N := (N : ℝ)) (β := β) hN1 hβ0
        (k := ⌊(N : ℝ) ^ (1 / β)⌋₊ + 1) (by omega) hkN hkge
    -- the two endpoint gaps
    have hLone : (1 : ℝ) ≤ Real.log (N : ℝ) := by linarith
    have hgap1 := phi_lower_gap hN64 hα hα15
      (log_upper_cutoff_ge hN64 hα hα15 hL167) hb1' hble hLone hca
    have hgap2 := phi_upper_gap hN64 hβ0 hβ
      (log_lower_cutoff_ge (by omega : 1 ≤ N) hβ0 hβ) hk1 hkge hLone hbd
    -- the two char_sum applications
    have hanalytic := char_sum_ge hNterm hα hαβ hα15 hβ0 hβ hFmono hFnn (le_of_lt hε0) hε64 hθN
      (log_lower_cutoff_ge (by omega : 1 ≤ N) hβ0 hβ)
      (log_upper_cutoff_ge hN64 hα hα15 hL167) hgap1 hgap2 hltN
    have hupper := char_sum_le hNterm hα hαβ hα15 hβ0 hβ (monotone_const) (fun _ => zero_le_one)
      (le_of_lt hε0) hε64 hθN (log_lower_cutoff_ge (by omega : 1 ≤ N) hβ0 hβ)
      (log_upper_cutoff_ge hN64 hα hα15 hL167)
    simp only [one_mul] at hupper
    -- replace the integral of F by the integral of L
    have hFint : ∀ᵉ (z : ℝ), z ∈ Set.uIcc (α - 1) (β - 1) → F z = L z := by
      intro z hz
      rw [Set.uIcc_of_le (by linarith : α - 1 ≤ β - 1)] at hz
      show max (L z) 0 = L z
      rw [max_eq_left (hL0 z ⟨by linarith [hz.1], by linarith [hz.2]⟩)]
    have hintEq : (∫ z in (α - 1)..(β - 1), F z * Kernel616.kernel z)
        = ∫ z in (α - 1)..(β - 1), L z * Kernel616.kernel z := by
      apply intervalIntegral.integral_congr
      intro z hz
      show F z * Kernel616.kernel z = L z * Kernel616.kernel z
      rw [hFint z hz]
    rw [hintEq] at hanalytic
    -- the weight, and the pointwise lower bound from the auxiliary hypothesis
    set W : ℕ → ℝ := fun p => 1 / ((p : ℝ) * (Real.log ((N : ℝ) / p)) ^ 2) with hWdef
    have htkm : ∀ p ∈ primeBand N (cutoff N β) (cutoff N α),
        ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) ≤ (p : ℝ) ∧
          (p : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / α)⌋₊ : ℕ) : ℝ) := by
      intro p hp
      obtain ⟨-, hpp, hw, hz⟩ := Finset.mem_filter.mp hp
      refine ⟨?_, ?_⟩
      · rw [cutoff_eq_coe_succ] at hw
        exact hw
      · have hpcut : p < ⌊(N : ℝ) ^ (1 / α)⌋₊ + 1 := by
          rw [cutoff_eq_coe_succ] at hz
          exact_mod_cast hz
        have hle : p ≤ ⌊(N : ℝ) ^ (1 / α)⌋₊ := by omega
        exact_mod_cast hle
    have hA : ∀ p ∈ (primeBand N (cutoff N β) (cutoff N α)).filter (fun p => p.Coprime N),
        2 * (L (Real.log ((N : ℝ) / p) / Real.log p) - δ) * M T N * (Real.log (N : ℝ)) ^ 2 * W p
          ≤ childMass N p := by
      intro p hp
      obtain ⟨hpband, hpcop⟩ := Finset.mem_filter.mp hp
      obtain ⟨-, hpp, hw, hz⟩ := Finset.mem_filter.mp hpband
      have h := hauxN hEven p hpp hpcop hw hz
      have heq : 2 * (L (Real.log ((N : ℝ) / p) / Real.log p) - δ) * M T N *
          (Real.log (N : ℝ)) ^ 2 * W p
          = 2 * (L (Real.log ((N : ℝ) / p) / Real.log p) - δ) * M T N *
            (Real.log (N : ℝ)) ^ 2 / ((p : ℝ) * (Real.log ((N : ℝ) / p)) ^ 2) := by
        rw [hWdef]
        ring
      rw [heq]
      exact h
    -- the removed mass is at least the coprime band sum
    have hremsum : 2 * M T N * (Real.log (N : ℝ)) ^ 2 *
        (∑ p ∈ (primeBand N (cutoff N β) (cutoff N α)).filter (fun p => p.Coprime N),
          (F (Real.log ((N : ℝ) / p) / Real.log p) - δ) * W p)
        ≤ (Finite616.removed N (cutoff N β) (cutoff N α)).re := by
      rw [removed_eq_sum_coprime (N := N) (by omega : 1 < N) (cutoff N β) (cutoff N α)]
      have h1 : 2 * M T N * (Real.log (N : ℝ)) ^ 2 *
          (∑ p ∈ (primeBand N (cutoff N β) (cutoff N α)).filter (fun p => p.Coprime N),
            (F (Real.log ((N : ℝ) / p) / Real.log p) - δ) * W p)
          = ∑ p ∈ (primeBand N (cutoff N β) (cutoff N α)).filter (fun p => p.Coprime N),
              2 * (L (Real.log ((N : ℝ) / p) / Real.log p) - δ) * M T N *
                (Real.log (N : ℝ)) ^ 2 * W p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        obtain ⟨hpband, -⟩ := Finset.mem_filter.mp hp
        obtain ⟨htk, htm⟩ := htkm p hpband
        obtain ⟨hφ2, hφ14⟩ := phi_mem hN64 hα hαβ hβ0 hβ hα15 htk htm
        have hFL : F (Real.log ((N : ℝ) / p) / Real.log p) = L (Real.log ((N : ℝ) / p) / Real.log p) := by
          show max (L (Real.log ((N : ℝ) / p) / Real.log p)) 0 = L (Real.log ((N : ℝ) / p) / Real.log p)
          rw [max_eq_left (hL0 _ ⟨hφ2, hφ14⟩)]
        rw [hFL]
        ring
      rw [h1]
      exact Finset.sum_le_sum hA
    -- the primes of the band that divide N contribute a negligible mass
    have hWbound : ∀ p ∈ (primeBand N (cutoff N β) (cutoff N α)).filter (fun p => ¬ p.Coprime N),
        W p ≤ 9 / (4 * (N : ℝ) ^ ((1 : ℝ) / 15) * (Real.log (N : ℝ)) ^ 2) := by
      intro p hp
      obtain ⟨hpband, hncop⟩ := Finset.mem_filter.mp hp
      obtain ⟨-, hpp, hw, hz⟩ := Finset.mem_filter.mp hpband
      obtain ⟨htk, htm⟩ := htkm p hpband
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
      have hpN : (p : ℝ) < (N : ℝ) := lt_of_le_of_lt (htkm p hpband).2 hbNlt
      have hlogp : (0 : ℝ) < Real.log ((N : ℝ) / p) := by
        apply Real.log_pos
        rw [one_lt_div hp0]
        linarith
      have h151 : (2 : ℝ) * Real.log (N : ℝ) / 3 ≤ Real.log ((N : ℝ) / p) := by
        have hble' : (p : ℝ) ≤ (N : ℝ) ^ (1 / α) := le_trans htm (Nat.floor_le (by positivity))
        have hpN1 : (N : ℝ) / p ≥ (N : ℝ) ^ (1 - 1 / α) := by
          have hstep : (N : ℝ) / (N : ℝ) ^ (1 / α) ≤ (N : ℝ) / p :=
            div_le_div_of_nonneg_left (le_of_lt hN0) hp0 hble'
          have hrp : (N : ℝ) / (N : ℝ) ^ (1 / α) = (N : ℝ) ^ (1 - 1 / α) := by
            have h := Real.rpow_sub hN0 (1 : ℝ) (1 / α)
            rw [Real.rpow_one] at h
            exact h.symm
          linarith [hstep, hrp]
        have hlog2 : Real.log ((N : ℝ) ^ (1 - 1 / α)) = (1 - 1 / α) * Real.log (N : ℝ) :=
          Real.log_rpow hN0 _
        have hmono := Real.log_le_log (Real.rpow_pos_of_pos hN0 _) hpN1
        rw [hlog2] at hmono
        have : (1 - 1 / α) * Real.log (N : ℝ) ≥ 2 * Real.log (N : ℝ) / 3 := by
          have hα3 : (1 : ℝ) / α ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hα
          nlinarith [hL]
        linarith
      -- the prime exceeds N^(1/15)
      have hpge : (N : ℝ) ^ ((1 : ℝ) / 15) ≤ (p : ℝ) := by
        have h1 : (N : ℝ) ^ ((1 : ℝ) / 15) ≤ (N : ℝ) ^ (1 / β) := by
          apply Real.rpow_le_rpow_of_exponent_le (le_of_lt hN1)
          have hβ1 : (1 : ℝ) / 15 ≤ 1 / β := one_div_le_one_div_of_le hβ0 hβ
          linarith
        refine le_trans h1 ?_
        have hlt' : (N : ℝ) ^ (1 / β) < ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by
          have h := Nat.lt_floor_add_one ((N : ℝ) ^ (1 / β))
          push_cast
          linarith
        linarith
      rw [hWdef]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hL2 : (0 : ℝ) < (Real.log (N : ℝ)) ^ 2 := by positivity
      have hsq : (2 * Real.log (N : ℝ) / 3) ^ 2 ≤ (Real.log ((N : ℝ) / p)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) h151 2
      nlinarith [hp0, hpge, hsq, hL2, Real.rpow_pos_of_pos hN0 ((1 : ℝ) / 15)]
    have hbadcard : ((primeBand N (cutoff N β) (cutoff N α)).filter (fun p => ¬ p.Coprime N)).card ≤ 15 := by
      refine bad_primes_card_le (by omega : 2 ≤ N) ?_ ?_ ?_
      · intro p hp
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
      · intro p hp
        obtain ⟨hpband, hncop⟩ := Finset.mem_filter.mp hp
        obtain ⟨-, hpp, -⟩ := Finset.mem_filter.mp hpband
        by_contra hd
        exact hncop (hpp.coprime_iff_not_dvd.mpr hd)
      · intro p hp
        obtain ⟨hpband, -⟩ := Finset.mem_filter.mp hp
        have h1 : (N : ℝ) ^ ((1 : ℝ) / 15) ≤ (N : ℝ) ^ (1 / β) := by
          apply Real.rpow_le_rpow_of_exponent_le (le_of_lt hN1)
          have hβ1 : (1 : ℝ) / 15 ≤ 1 / β := one_div_le_one_div_of_le hβ0 hβ
          linarith
        refine le_trans h1 ?_
        have hlt' : (N : ℝ) ^ (1 / β) < ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by
          have h := Nat.lt_floor_add_one ((N : ℝ) ^ (1 / β))
          push_cast
          linarith
        linarith [(htkm p hpband).1]
    have hbadmass : (∑ p ∈ (primeBand N (cutoff N β) (cutoff N α)).filter (fun p => ¬ p.Coprime N), W p)
        ≤ 135 / (4 * (N : ℝ) ^ ((1 : ℝ) / 15) * (Real.log (N : ℝ)) ^ 2) := by
      have h1 : (∑ p ∈ (primeBand N (cutoff N β) (cutoff N α)).filter (fun p => ¬ p.Coprime N), W p)
          ≤ ∑ p ∈ (primeBand N (cutoff N β) (cutoff N α)).filter (fun p => ¬ p.Coprime N),
              9 / (4 * (N : ℝ) ^ ((1 : ℝ) / 15) * (Real.log (N : ℝ)) ^ 2) :=
        Finset.sum_le_sum hWbound
      have h2 : (∑ p ∈ (primeBand N (cutoff N β) (cutoff N α)).filter (fun p => ¬ p.Coprime N),
            9 / (4 * (N : ℝ) ^ ((1 : ℝ) / 15) * (Real.log (N : ℝ)) ^ 2))
          = ((primeBand N (cutoff N β) (cutoff N α)).filter (fun p => ¬ p.Coprime N)).card *
            (9 / (4 * (N : ℝ) ^ ((1 : ℝ) / 15) * (Real.log (N : ℝ)) ^ 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have h3 : (((primeBand N (cutoff N β) (cutoff N α)).filter (fun p => ¬ p.Coprime N)).card : ℝ) ≤ 15 := by
        exact_mod_cast hbadcard
      have h4 : (0 : ℝ) < 4 * (N : ℝ) ^ ((1 : ℝ) / 15) * (Real.log (N : ℝ)) ^ 2 := by positivity
      rw [h2] at h1
      have h4' : (0 : ℝ) ≤ 9 / (4 * (N : ℝ) ^ ((1 : ℝ) / 15) * (Real.log (N : ℝ)) ^ 2) := by positivity
      have h5 : (((primeBand N (cutoff N β) (cutoff N α)).filter
            (fun p => ¬ p.Coprime N)).card : ℝ) *
            (9 / (4 * (N : ℝ) ^ ((1 : ℝ) / 15) * (Real.log (N : ℝ)) ^ 2))
          ≤ 15 * (9 / (4 * (N : ℝ) ^ ((1 : ℝ) / 15) * (Real.log (N : ℝ)) ^ 2)) := by
        nlinarith [h3, h4']
      have h6 : 15 * (9 / (4 * (N : ℝ) ^ ((1 : ℝ) / 15) * (Real.log (N : ℝ)) ^ 2))
          = 135 / (4 * (N : ℝ) ^ ((1 : ℝ) / 15) * (Real.log (N : ℝ)) ^ 2) := by
        field_simp
        ring
      linarith [h1, h5, h6]
    -- the coprime band sum against the full band sum
    have hcop : (∑ p ∈ (primeBand N (cutoff N β) (cutoff N α)).filter (fun p => p.Coprime N),
          (F (Real.log ((N : ℝ) / p) / Real.log p) - δ) * W p)
        ≥ (∑ p ∈ primeBand N (cutoff N β) (cutoff N α),
            (F (Real.log ((N : ℝ) / p) / Real.log p) - δ) * W p)
          - X * (135 / (4 * (N : ℝ) ^ ((1 : ℝ) / 15) * (Real.log (N : ℝ)) ^ 2)) := by
      have hsplitf : (∑ p ∈ primeBand N (cutoff N β) (cutoff N α),
            (F (Real.log ((N : ℝ) / p) / Real.log p) - δ) * W p)
          = (∑ p ∈ (primeBand N (cutoff N β) (cutoff N α)).filter (fun p => p.Coprime N),
              (F (Real.log ((N : ℝ) / p) / Real.log p) - δ) * W p)
            + ∑ p ∈ (primeBand N (cutoff N β) (cutoff N α)).filter (fun p => ¬ p.Coprime N),
              (F (Real.log ((N : ℝ) / p) / Real.log p) - δ) * W p :=
        (Finset.sum_filter_add_sum_filter_not (s := primeBand N (cutoff N β) (cutoff N α))
          (p := fun p => p.Coprime N) (f := fun p => (F (Real.log ((N : ℝ) / p) / Real.log p) - δ) * W p)).symm
      have hbnd : (∑ p ∈ (primeBand N (cutoff N β) (cutoff N α)).filter (fun p => ¬ p.Coprime N),
            (F (Real.log ((N : ℝ) / p) / Real.log p) - δ) * W p)
          ≤ X * (135 / (4 * (N : ℝ) ^ ((1 : ℝ) / 15) * (Real.log (N : ℝ)) ^ 2)) := by
        have h1 : (∑ p ∈ (primeBand N (cutoff N β) (cutoff N α)).filter (fun p => ¬ p.Coprime N),
              (F (Real.log ((N : ℝ) / p) / Real.log p) - δ) * W p)
            ≤ ∑ p ∈ (primeBand N (cutoff N β) (cutoff N α)).filter (fun p => ¬ p.Coprime N),
                X * W p := by
          apply Finset.sum_le_sum
          intro p hp
          obtain ⟨hpband, -⟩ := Finset.mem_filter.mp hp
          obtain ⟨htk, htm⟩ := htkm p hpband
          obtain ⟨hφ2, hφ14⟩ := phi_mem hN64 hα hαβ hβ0 hβ hα15 htk htm
          have hFle : F (Real.log ((N : ℝ) / p) / Real.log p) ≤ X := by
            rw [hXdef]
            exact (hFmono hφ14).trans (le_max_right _ _)
          have hp0 : (0 : ℝ) < (p : ℝ) := by
            have hk3r : (3 : ℝ) ≤ ((⌊(N : ℝ) ^ (1 / β)⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hk3
            linarith [(htkm p hpband).1]
          have hW0 : (0 : ℝ) ≤ W p := by
            rw [hWdef]
            have hlogp : (0 : ℝ) < Real.log ((N : ℝ) / p) := by
              apply Real.log_pos
              rw [one_lt_div hp0]
              linarith [(htkm p hpband).2]
            positivity
          have h1' : (F (Real.log ((N : ℝ) / p) / Real.log p) - δ) * W p
              ≤ F (Real.log ((N : ℝ) / p) / Real.log p) * W p := by
            nlinarith [hW0, le_of_lt hδ0]
          have h2' : F (Real.log ((N : ℝ) / p) / Real.log p) * W p ≤ X * W p :=
            mul_le_mul_of_nonneg_right hFle hW0
          linarith
        have h2 : (∑ p ∈ (primeBand N (cutoff N β) (cutoff N α)).filter (fun p => ¬ p.Coprime N),
              X * W p)
            = X * (∑ p ∈ (primeBand N (cutoff N β) (cutoff N α)).filter (fun p => ¬ p.Coprime N), W p) := by
          rw [Finset.mul_sum]
        rw [h2] at h1
        nlinarith [h1, hbadmass, hXnn]
      linarith [hsplitf, hbnd]
    -- combine: the band sum of `F - δ` against the two integral bounds
    have hband_sub : (∑ p ∈ primeBand N (cutoff N β) (cutoff N α),
          (F (Real.log ((N : ℝ) / p) / Real.log p) - δ) * W p)
        = (∑ p ∈ primeBand N (cutoff N β) (cutoff N α),
            F (Real.log ((N : ℝ) / p) / Real.log p) * W p)
          - δ * (∑ p ∈ primeBand N (cutoff N β) (cutoff N α), W p) := by
      have hpt : (∑ p ∈ primeBand N (cutoff N β) (cutoff N α),
            (F (Real.log ((N : ℝ) / p) / Real.log p) - δ) * W p)
          = ∑ p ∈ primeBand N (cutoff N β) (cutoff N α),
              (F (Real.log ((N : ℝ) / p) / Real.log p) * W p - δ * W p) := by
        apply Finset.sum_congr rfl
        intro p hp
        ring
      rw [hpt, Finset.sum_sub_distrib, Finset.mul_sum]
    have hupper' : (Real.log (N : ℝ)) ^ 2 *
        (∑ p ∈ primeBand N (cutoff N β) (cutoff N α), W p)
        ≤ J1 + 4 * ε * J1 + 500 * (Real.log (N : ℝ))⁻¹ := by
      have h2 : max (1 : ℝ) 1 = 1 := max_self 1
      rw [h2] at hupper
      have h3 : 500 * 1 / Real.log (N : ℝ) = 500 * (Real.log (N : ℝ))⁻¹ := by
        ring
      rw [h3] at hupper
      exact hupper
    -- the six budget terms
    have hc1 : 1000 * X / Real.log (N : ℝ) ≤ η / 8 := by
      rw [div_le_iff₀ hL]
      have h := mul_le_mul_of_nonneg_left hL4000 (le_of_lt (by positivity : (0 : ℝ) < η / 8))
      have heq : η / 8 * (16000 * X / η) = 2000 * X := by
        field_simp <;> ring
      rw [heq] at h
      linarith
    have hc2 : 1000 * δ / Real.log (N : ℝ) ≤ η / 8 := by
      have hpos : (0 : ℝ) < J1 + 1 := by linarith
      have h16 := mul_le_mul_of_nonneg_left hL16 (by positivity : (0 : ℝ) ≤ η / 8)
      have heq : η / 8 * (16 * (J1 + 1)⁻¹) = 2 * η / (J1 + 1) := by
        field_simp
        ring
      rw [heq] at h16
      have hd1 : 1000 * δ ≤ 2 * η / (J1 + 1) := by
        rw [hδdef]
        rw [show 1000 * (η / (1024 * (J1 + 1))) = 1000 * η / (1024 * (J1 + 1)) by ring]
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 1024 * (J1 + 1)) hpos]
        nlinarith [hη, hpos]
      rw [div_le_iff₀ hL]
      linarith
    have hbudget : 2 * (4 * ε * J + 960 * X * (N : ℝ) ^ (-(1 / 15 : ℝ)) + 500 * X * (Real.log (N : ℝ))⁻¹
        + δ * (J1 + 4 * ε * J1 + 500 * (Real.log (N : ℝ))⁻¹)
        + 135 / 4 * X * (N : ℝ) ^ (-(1 / 15 : ℝ))) ≤ η := by
      have hrp : (2000 * X) * (N : ℝ) ^ (-(1 / 15 : ℝ)) ≤ η / 8 := hrpowN
      have hexp : 2 * (4 * ε * J + 960 * X * (N : ℝ) ^ (-(1 / 15 : ℝ)) + 500 * X * (Real.log (N : ℝ))⁻¹
          + δ * (J1 + 4 * ε * J1 + 500 * (Real.log (N : ℝ))⁻¹)
          + 135 / 4 * X * (N : ℝ) ^ (-(1 / 15 : ℝ)))
          = 8 * ε * J + (1920 * X + 135 / 2 * X) * (N : ℝ) ^ (-(1 / 15 : ℝ))
            + 1000 * X * (Real.log (N : ℝ))⁻¹ + 2 * (δ * J1) + 8 * ε * (δ * J1)
            + 1000 * δ * (Real.log (N : ℝ))⁻¹ := by
        ring
      rw [hexp]
      have hcomb : (1920 * X + 135 / 2 * X) * (N : ℝ) ^ (-(1 / 15 : ℝ)) ≤ η / 8 := by
        nlinarith [hrp]
      have h8 : 500 * X * (Real.log (N : ℝ))⁻¹ ≤ η / 8 := by
        have hhalf : 500 * X * (Real.log (N : ℝ))⁻¹ = (1000 * X / Real.log (N : ℝ)) / 2 := by
          rw [div_eq_mul_inv]
          ring
        rw [hhalf]
        linarith [hc1, hη]
      have h9 : 1000 * δ * (Real.log (N : ℝ))⁻¹ ≤ η / 8 := by
        have hhalf : 1000 * δ * (Real.log (N : ℝ))⁻¹ = (1000 * δ / Real.log (N : ℝ)) := by
          rw [div_eq_mul_inv]
        rw [hhalf]
        exact hc2
      linarith [hb1, hb2, hb3, hc1, hc2, hcomb]
    -- finish
    have hL2 : (0 : ℝ) < (Real.log (N : ℝ)) ^ 2 := by positivity
    have hN15 : (N : ℝ) ^ ((1 : ℝ) / 15) ≠ 0 := (Real.rpow_pos_of_pos hN0 _).ne'
    have hrpoweq : (N : ℝ) ^ (-(1 / 15 : ℝ)) = ((N : ℝ) ^ ((1 : ℝ) / 15))⁻¹ :=
      Real.rpow_neg hN0.le ((1 : ℝ) / 15)
    have hbudgetM : M T N * (2 * (4 * ε * J + 960 * X * (N : ℝ) ^ (-(1 / 15 : ℝ))
        + 500 * X * (Real.log (N : ℝ))⁻¹
        + δ * (J1 + 4 * ε * J1 + 500 * (Real.log (N : ℝ))⁻¹)
        + 135 / 4 * X * (N : ℝ) ^ (-(1 / 15 : ℝ)))) ≤ M T N * η :=
      mul_le_mul_of_nonneg_left hbudget hMnn
    have hchain : 2 * M T N * (J - 4 * ε * J - 960 * X * (N : ℝ) ^ (-(1 / 15 : ℝ))
        - 500 * X * (Real.log (N : ℝ))⁻¹
        - δ * (J1 + 4 * ε * J1 + 500 * (Real.log (N : ℝ))⁻¹)
        - 135 / 4 * X * (N : ℝ) ^ (-(1 / 15 : ℝ))) ≤
        (Finite616.removed N (cutoff N β) (cutoff N α)).re := by
      have h1 : 2 * M T N * (Real.log (N : ℝ)) ^ 2 *
          ((∑ p ∈ primeBand N (cutoff N β) (cutoff N α),
              (F (Real.log ((N : ℝ) / p) / Real.log p) - δ) * W p)
            - X * (135 / (4 * (N : ℝ) ^ ((1 : ℝ) / 15) * (Real.log (N : ℝ)) ^ 2)))
          ≤ 2 * M T N * (Real.log (N : ℝ)) ^ 2 *
            (∑ p ∈ (primeBand N (cutoff N β) (cutoff N α)).filter (fun p => p.Coprime N),
              (F (Real.log ((N : ℝ) / p) / Real.log p) - δ) * W p) := by
        apply mul_le_mul_of_nonneg_left hcop
        positivity
      have h3 : 2 * M T N * (Real.log (N : ℝ)) ^ 2 *
          ((∑ p ∈ primeBand N (cutoff N β) (cutoff N α),
              (F (Real.log ((N : ℝ) / p) / Real.log p) - δ) * W p)
            - X * (135 / (4 * (N : ℝ) ^ ((1 : ℝ) / 15) * (Real.log (N : ℝ)) ^ 2)))
          = 2 * M T N * ((Real.log (N : ℝ)) ^ 2 *
              (∑ p ∈ primeBand N (cutoff N β) (cutoff N α),
                (F (Real.log ((N : ℝ) / p) / Real.log p) - δ) * W p))
            - 2 * M T N * (X * (135 / (4 * (N : ℝ) ^ ((1 : ℝ) / 15)))) := by
        field_simp <;> ring
      rw [h3] at h1
      rw [hband_sub] at h1
      have h4 : (Real.log (N : ℝ)) ^ 2 *
          ((∑ p ∈ primeBand N (cutoff N β) (cutoff N α),
              F (Real.log ((N : ℝ) / p) / Real.log p) * W p)
            - δ * (∑ p ∈ primeBand N (cutoff N β) (cutoff N α), W p))
          = (Real.log (N : ℝ)) ^ 2 *
              (∑ p ∈ primeBand N (cutoff N β) (cutoff N α),
                F (Real.log ((N : ℝ) / p) / Real.log p) * W p)
            - δ * ((Real.log (N : ℝ)) ^ 2 *
              (∑ p ∈ primeBand N (cutoff N β) (cutoff N α), W p)) := by ring
      rw [h4] at h1
      have hNpn : (0 : ℝ) ≤ (N : ℝ) ^ (-(1 / 15 : ℝ)) := Real.rpow_nonneg hN0.le _
      have hanaM : 2 * M T N * (J - 4 * ε * J - 960 * X * (N : ℝ) ^ (-(1 / 15 : ℝ))
          - 500 * X * (Real.log (N : ℝ))⁻¹)
          ≤ 2 * M T N * ((Real.log (N : ℝ)) ^ 2 *
              (∑ p ∈ primeBand N (cutoff N β) (cutoff N α),
                F (Real.log ((N : ℝ) / p) / Real.log p) * W p)) :=
        mul_le_mul_of_nonneg_left hanalytic (by linarith : (0 : ℝ) ≤ 2 * M T N)
      have huppM : 2 * M T N * (δ * ((Real.log (N : ℝ)) ^ 2 *
            (∑ p ∈ primeBand N (cutoff N β) (cutoff N α), W p)))
          ≤ 2 * M T N * (δ * (J1 + 4 * ε * J1 + 500 * (Real.log (N : ℝ))⁻¹)) := by
        have hd : δ * ((Real.log (N : ℝ)) ^ 2 *
            (∑ p ∈ primeBand N (cutoff N β) (cutoff N α), W p))
            ≤ δ * (J1 + 4 * ε * J1 + 500 * (Real.log (N : ℝ))⁻¹) :=
          mul_le_mul_of_nonneg_left hupper' (le_of_lt hδ0)
        exact mul_le_mul_of_nonneg_left hd (by linarith : (0 : ℝ) ≤ 2 * M T N)
      have h5 := h1.trans hremsum
      have hC : 2 * M T N * (X * (135 / (4 * (N : ℝ) ^ ((1 : ℝ) / 15))))
          = 2 * M T N * (135 / 4 * X * (N : ℝ) ^ (-(1 / 15 : ℝ))) := by
        rw [hrpoweq]
        ring
      rw [hC] at h5
      have key : 2 * M T N * (J - 4 * ε * J - 960 * X * (N : ℝ) ^ (-(1 / 15 : ℝ))
          - 500 * X * (Real.log (N : ℝ))⁻¹
          - δ * (J1 + 4 * ε * J1 + 500 * (Real.log (N : ℝ))⁻¹)
          - 135 / 4 * X * (N : ℝ) ^ (-(1 / 15 : ℝ)))
          = 2 * M T N * (J - 4 * ε * J - 960 * X * (N : ℝ) ^ (-(1 / 15 : ℝ))
              - 500 * X * (Real.log (N : ℝ))⁻¹)
            - 2 * M T N * (δ * (J1 + 4 * ε * J1 + 500 * (Real.log (N : ℝ))⁻¹))
            - 2 * M T N * (135 / 4 * X * (N : ℝ) ^ (-(1 / 15 : ℝ))) := by ring
      rw [key]
      have hsum2 : 192 * X + 0 = 192 * X := by ring
      linarith [h5, hanaM, huppM]
    have hstep : 2 * M T N * J - M T N * η
        ≤ 2 * M T N * (J - 4 * ε * J - 960 * X * (N : ℝ) ^ (-(1 / 15 : ℝ))
          - 500 * X * (Real.log (N : ℝ))⁻¹
          - δ * (J1 + 4 * ε * J1 + 500 * (Real.log (N : ℝ))⁻¹)
          - 135 / 4 * X * (N : ℝ) ^ (-(1 / 15 : ℝ))) := by
      have hexp2 : 2 * M T N * (J - 4 * ε * J - 960 * X * (N : ℝ) ^ (-(1 / 15 : ℝ))
          - 500 * X * (Real.log (N : ℝ))⁻¹
          - δ * (J1 + 4 * ε * J1 + 500 * (Real.log (N : ℝ))⁻¹)
          - 135 / 4 * X * (N : ℝ) ^ (-(1 / 15 : ℝ)))
          = 2 * M T N * J - M T N * (2 * (4 * ε * J + 960 * X * (N : ℝ) ^ (-(1 / 15 : ℝ))
            + 500 * X * (Real.log (N : ℝ))⁻¹
            + δ * (J1 + 4 * ε * J1 + 500 * (Real.log (N : ℝ))⁻¹)
            + 135 / 4 * X * (N : ℝ) ^ (-(1 / 15 : ℝ)))) := by ring
      rw [hexp2]
      linarith [hbudgetM]
    have hgoal : (2 * J - η) * M T N = 2 * M T N * J - M T N * η := by ring
    rw [hgoal]
    linarith [hchain, hstep]

end LeanLab.AlmostPrimeSums.Decomp616
