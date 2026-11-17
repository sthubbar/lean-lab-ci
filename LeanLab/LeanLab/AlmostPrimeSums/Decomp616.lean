/-
AI wrote the Lean code. Goldbach is open.
Task616 U-1690. P0072 p. 63 seeds and Buchstab1938 pp. 381 to 383 transfers.
The transfer leaves retain uniform auxiliary domain hypotheses explicitly.
The extension of the printed range ten to fifteen is OPEN.
-/
import LeanLab.AlmostPrimeSums.Finite616
import LeanLab.AlmostPrimeSums.Kernel616
import LeanLab.AlmostPrimeSums.TogashiUchiyamaScale

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
  sorry

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
  sorry

end LeanLab.AlmostPrimeSums.Decomp616
