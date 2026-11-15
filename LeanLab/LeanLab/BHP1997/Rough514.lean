/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17 with page 3, display 1.8.

The Siegel Walfisz input for a rough variable. On page 51 the paper obtains 5.17 for the
subtracted sums of 5.15 from the Siegel Walfisz theorem applied inside the rough variable.
This file carries that step for one rough variable on one interval: a rough integer above one
is written as its largest prime factor times a cofactor, and the prime character sum over the
largest prime factor is bounded by the lab prime input `Prime514.character_prime_prefix_bound`.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Prime514
import LeanLab.BHP1997.Rough308

namespace LeanLab.BHP1997.Rough514
open Classical Complex Decomp132
open scoped BigOperators

/-- P0069 page 51 display 5.17. Every integer above one has a largest prime factor. This is
the prime variable in which the Siegel Walfisz theorem is applied. -/
theorem exists_largest_prime_factor {n : ℕ} (hn : 2 ≤ n) :
    ∃ P : ℕ, P.Prime ∧ P ∣ n ∧ ∀ r : ℕ, r.Prime → r ∣ n → r ≤ P := by
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  obtain ⟨P, hP, hmax⟩ := Finset.exists_max_image n.primeFactors id hne
  have hP' := Nat.mem_primeFactors.mp hP
  exact ⟨P, hP'.1, hP'.2.1, fun r hr hrn =>
    hmax r (Nat.mem_primeFactors.mpr ⟨hr, hrn, by omega⟩)⟩

/-- P0069 page 51 display 5.17. A prime times a cofactor has no prime factor below the cutoff
exactly when the prime is at least the cutoff and the cofactor is rough. -/
theorem rough_prime_mul {P m z : ℕ} (hP : P.Prime) :
    Task308.roughIndicator (P * m) z =
      if z ≤ P then Task308.roughIndicator m z else 0 := by
  have h01 : ∀ n : ℕ, Task308.roughIndicator n z = 0 ∨ Task308.roughIndicator n z = 1 := by
    intro n
    unfold Task308.roughIndicator
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  have key : Task308.roughIndicator (P * m) z = 1 ↔
      (z ≤ P ∧ Task308.roughIndicator m z = 1) := by
    rw [Task308.rough_indicator_support, Task308.rough_indicator_support]
    constructor
    · intro h
      refine ⟨?_, fun p hp hpz hpm => h p hp hpz (dvd_mul_of_dvd_right hpm P)⟩
      by_contra hz
      exact h P hP (by omega) (dvd_mul_right P m)
    · rintro ⟨hz, h⟩ p hp hpz hpm
      rcases (Nat.Prime.dvd_mul hp).mp hpm with h1 | h1
      · have := (Nat.prime_dvd_prime_iff_eq hp hP).mp h1
        omega
      · exact h p hp hpz h1
  by_cases hz : z ≤ P
  · rw [if_pos hz]
    rcases h01 m with h2 | h2
    · rw [h2]
      rcases h01 (P * m) with h1 | h1
      · exact h1
      · exact absurd (key.mp h1).2 (by rw [h2]; norm_num)
    · rw [h2]
      exact key.mpr ⟨hz, h2⟩
  · rw [if_neg hz]
    rcases h01 (P * m) with h1 | h1
    · exact h1
    · exact absurd (key.mp h1).1 hz

/-- P0069 page 51 display 5.17. An integer above one is in exactly one way a prime times a
cofactor all of whose prime factors are at most that prime. -/
theorem largest_prime_decomp (b n : ℕ) (hn : 2 ≤ n) (hnb : n ≤ b) (v : ℂ) :
    ∑ x ∈ Finset.Icc 1 b ×ˢ Finset.Icc 1 b,
      (if x.2 * x.1 = n ∧ x.2.Prime ∧ x.1.primeFactors.sup id ≤ x.2 then v else 0) = v := by
  obtain ⟨P0, hP0, hdvd, hmax⟩ := exists_largest_prime_factor hn
  have hmul : P0 * (n / P0) = n := Nat.mul_div_cancel' hdvd
  rw [Finset.sum_eq_single (n / P0, P0)]
  · rw [if_pos]
    refine ⟨hmul, hP0, Finset.sup_le fun r hr => ?_⟩
    exact hmax r (Nat.prime_of_mem_primeFactors hr)
      ((Nat.dvd_of_mem_primeFactors hr).trans (Dvd.intro_left _ hmul))
  · intro x hx hne
    rw [if_neg]
    rintro ⟨h1, h2, h3⟩
    apply hne
    have hx1 : 1 ≤ x.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hx).1).1
    have hP : x.2 = P0 := by
      have hle : x.2 ≤ P0 := hmax x.2 h2 (Dvd.intro _ h1)
      have hd : P0 ∣ x.2 * x.1 := by rw [h1]; exact hdvd
      rcases (Nat.Prime.dvd_mul hP0).mp hd with h | h
      · exact ((Nat.prime_dvd_prime_iff_eq hP0 h2).mp h).symm
      · have hmem : P0 ∈ x.1.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hP0, h, by omega⟩
        have : id P0 ≤ x.1.primeFactors.sup id := Finset.le_sup hmem
        exact le_antisymm hle (this.trans h3)
    have hm : x.1 = n / P0 := by
      apply Nat.eq_of_mul_eq_mul_left hP0.pos
      rw [hmul, ← hP, h1]
    exact Prod.ext hm hP
  · intro hnot
    exfalso
    apply hnot
    have hP1 : 1 ≤ P0 := hP0.pos
    have hPn : P0 ≤ n := Nat.le_of_dvd (by omega) hdvd
    have hm0 : n / P0 ≠ 0 := by
      intro h0
      rw [h0] at hmul
      omega
    have hmn : n / P0 ≤ n := Nat.div_le_self _ _
    simp only [Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨Nat.pos_of_ne_zero hm0, hmn.trans hnb⟩, hP1, hPn.trans hnb⟩

/-- P0069 page 51 display 5.17. The rough character sum on an interval, reindexed by the
cofactor and the largest prime factor. For each cofactor the largest prime factor runs over
the primes of an integer interval. -/
theorem rough_sum_reindex {q : ℕ} (χ : DirichletCharacter ℂ q) (z a b : ℕ) (ha : 1 ≤ a)
    (hz : 1 ≤ z) :
    ∑ n ∈ Finset.Ioc a b, ((Task308.roughIndicator n z : ℝ) : ℂ) * χ (n : ZMod q) =
      ∑ m ∈ Finset.Icc 1 b, ((Task308.roughIndicator m z : ℝ) : ℂ) * χ (m : ZMod q) *
        ∑ P ∈ Finset.Ioc (max (a / m) (max z (m.primeFactors.sup id) - 1)) (b / m),
          (primeWeight P : ℂ) * χ (P : ZMod q) := by
  have h1 : ∑ n ∈ Finset.Ioc a b, ((Task308.roughIndicator n z : ℝ) : ℂ) * χ (n : ZMod q) =
      ∑ n ∈ Finset.Ioc a b, ∑ x ∈ Finset.Icc 1 b ×ˢ Finset.Icc 1 b,
        (if x.2 * x.1 = n ∧ x.2.Prime ∧ x.1.primeFactors.sup id ≤ x.2 then
          ((Task308.roughIndicator n z : ℝ) : ℂ) * χ (n : ZMod q) else 0) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' := Finset.mem_Ioc.mp hn
    exact (largest_prime_decomp b n (by omega) hn'.2 _).symm
  rw [h1, Finset.sum_comm]
  have h2 : ∀ x ∈ Finset.Icc 1 b ×ˢ Finset.Icc 1 b,
      ∑ n ∈ Finset.Ioc a b,
        (if x.2 * x.1 = n ∧ x.2.Prime ∧ x.1.primeFactors.sup id ≤ x.2 then
          ((Task308.roughIndicator n z : ℝ) : ℂ) * χ (n : ZMod q) else 0) =
      (if x.2 * x.1 ∈ Finset.Ioc a b ∧ x.2.Prime ∧ x.1.primeFactors.sup id ≤ x.2 then
          ((Task308.roughIndicator (x.2 * x.1) z : ℝ) : ℂ) * χ ((x.2 * x.1 : ℕ) : ZMod q)
        else 0) := by
    intro x _
    by_cases hc : x.2 * x.1 ∈ Finset.Ioc a b ∧ x.2.Prime ∧ x.1.primeFactors.sup id ≤ x.2
    · rw [if_pos hc, Finset.sum_eq_single (x.2 * x.1)]
      · rw [if_pos ⟨rfl, hc.2⟩]
      · intro n _ hne
        rw [if_neg (fun h => hne h.1.symm)]
      · intro h
        exact absurd hc.1 h
    · rw [if_neg hc]
      apply Finset.sum_eq_zero
      intro n hn
      rw [if_neg]
      rintro ⟨h, hR⟩
      exact hc ⟨by rw [h]; exact hn, hR⟩
  rw [Finset.sum_congr rfl h2, Finset.sum_product]
  dsimp only
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hfilter : Finset.Ioc (max (a / m) (max z (m.primeFactors.sup id) - 1)) (b / m) =
      (Finset.Icc 1 b).filter
        (fun P => max (a / m) (max z (m.primeFactors.sup id) - 1) < P ∧ P ≤ b / m) := by
    ext P
    have hU : b / m ≤ b := Nat.div_le_self _ _
    simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hfilter, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  by_cases hp : P.Prime
  · have hw : primeWeight P = 1 := by simp [primeWeight, hp]
    have hχ : χ ((P * m : ℕ) : ZMod q) = χ (P : ZMod q) * χ (m : ZMod q) := by
      rw [Nat.cast_mul, map_mul]
    rw [rough_prime_mul hp, hχ, hw]
    have i1 : a / m < P ↔ a < P * m := Nat.div_lt_iff_lt_mul (by omega)
    have i2 : P ≤ b / m ↔ P * m ≤ b := Nat.le_div_iff_mul_le (by omega)
    by_cases hzP : z ≤ P
    · rw [if_pos hzP]
      have hiff : (P * m ∈ Finset.Ioc a b ∧ P.Prime ∧ m.primeFactors.sup id ≤ P) ↔
          (max (a / m) (max z (m.primeFactors.sup id) - 1) < P ∧ P ≤ b / m) := by
        rw [Finset.mem_Ioc, ← i1, ← i2]
        constructor
        · rintro ⟨⟨h3, h4⟩, -, h5⟩
          omega
        · rintro ⟨h3, h4⟩
          exact ⟨⟨by omega, h4⟩, hp, by omega⟩
      by_cases hc : P * m ∈ Finset.Ioc a b ∧ P.Prime ∧ m.primeFactors.sup id ≤ P
      · rw [if_pos hc, if_pos (hiff.mp hc), Complex.ofReal_one]
        ring
      · rw [if_neg hc, if_neg (fun h => hc (hiff.mpr h))]
        simp
    · rw [if_neg hzP]
      have hno : ¬ (max (a / m) (max z (m.primeFactors.sup id) - 1) < P ∧ P ≤ b / m) := by
        omega
      rw [if_neg hno]
      simp
  · have hw : primeWeight P = 0 := by simp [primeWeight, hp]
    rw [if_neg (fun h => hp h.2.1), hw]
    simp

/-- P0069 page 51 display 5.17. The prime character sum over the largest prime factor, for
one cofactor: a difference of two prefix sums, each bounded by the lab prime input at the
scale `b / m`. -/
theorem inner_prime_bound {c : ℝ} (hc : 0 < c) {A B K X : ℝ} (hB : 0 < B)
    (hpre : ∀ X : ℝ, 2 ≤ X → ∀ (q : ℕ) [NeZero q], 1 ≤ q →
        (q : ℝ) ≤ Real.sqrt X / Real.log X ^ B →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ u : ℝ, 0 ≤ u → u ≤ X →
          ‖∑ n ∈ Finset.Icc 1 ⌊u⌋₊, (primeWeight n : ℂ) * χ (n : ZMod q)‖ ≤
            (q : ℝ) * (K * X / Real.log X ^ (2 * A + 1)))
    (hK : 0 < K) (hA : 0 < A) (hX3 : 3 ≤ X) (hXc : 2 ≤ X ^ c)
    (hlp : Real.log X ^ (A + B) ≤ X ^ (c / 2))
    {q : ℕ} (hq : 1 ≤ q) (hqA : (q : ℝ) ≤ Real.log X ^ A)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {z : ℕ} (hz : X ^ c ≤ (z : ℝ))
    {b : ℕ} (hb : (b : ℝ) ≤ X) {m : ℕ} (hm : 1 ≤ m) (L : ℕ) (hL : z - 1 ≤ L) :
    ‖∑ P ∈ Finset.Ioc L (b / m), (primeWeight P : ℂ) * χ (P : ZMod q)‖ ≤
      2 * ((q : ℝ) * (K * ((b : ℝ) / m) / (c * Real.log X) ^ (2 * A + 1))) := by
  haveI : NeZero q := ⟨by omega⟩
  have hX0 : 0 < X := by linarith
  have hlog1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    exact (Real.exp_one_lt_three.le).trans hX3
  have hlog0 : 0 < Real.log X := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  by_cases hLU : L < b / m
  · have hzU : z ≤ b / m := by omega
    have hUX' : ((b / m : ℕ) : ℝ) ≤ (b : ℝ) / m := Nat.cast_div_le
    have hzX' : X ^ c ≤ (b : ℝ) / m :=
      hz.trans ((Nat.cast_le.mpr hzU).trans hUX')
    have hX'2 : (2 : ℝ) ≤ (b : ℝ) / m := hXc.trans hzX'
    have hX'X : (b : ℝ) / m ≤ X := by
      refine le_trans ?_ hb
      exact div_le_self (Nat.cast_nonneg b) (by exact_mod_cast hm)
    have hXc0 : 0 < X ^ c := by linarith
    have hlogX' : c * Real.log X ≤ Real.log ((b : ℝ) / m) := by
      rw [← Real.log_rpow hX0]
      exact Real.log_le_log hXc0 hzX'
    have hlogX'0 : 0 < Real.log ((b : ℝ) / m) := Real.log_pos (by linarith)
    have hlogX'X : Real.log ((b : ℝ) / m) ≤ Real.log X :=
      Real.log_le_log (by linarith) hX'X
    have hsqrt : X ^ (c / 2) ≤ Real.sqrt ((b : ℝ) / m) := by
      have : X ^ (c / 2) = Real.sqrt (X ^ c) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le]
        congr 1
        ring
      rw [this]
      exact Real.sqrt_le_sqrt hzX'
    have hcut : (q : ℝ) ≤ Real.sqrt ((b : ℝ) / m) / Real.log ((b : ℝ) / m) ^ B := by
      rw [le_div_iff₀ (Real.rpow_pos_of_pos hlogX'0 _)]
      calc (q : ℝ) * Real.log ((b : ℝ) / m) ^ B
          ≤ Real.log X ^ A * Real.log X ^ B :=
            mul_le_mul hqA (Real.rpow_le_rpow hlogX'0.le hlogX'X hB.le)
              (Real.rpow_nonneg hlogX'0.le _) (Real.rpow_nonneg hlog0.le _)
        _ = Real.log X ^ (A + B) := (Real.rpow_add hlog0 _ _).symm
        _ ≤ X ^ (c / 2) := hlp
        _ ≤ _ := hsqrt
    have hU := hpre ((b : ℝ) / m) hX'2 q hq hcut χ hχ ((b / m : ℕ) : ℝ)
      (Nat.cast_nonneg _) hUX'
    have hLb := hpre ((b : ℝ) / m) hX'2 q hq hcut χ hχ (L : ℝ)
      (Nat.cast_nonneg _) ((Nat.cast_le.mpr hLU.le).trans hUX')
    rw [Nat.floor_natCast] at hU hLb
    have hsplit := Finset.sum_Ioc_consecutive
      (fun P : ℕ => (primeWeight P : ℂ) * χ (P : ZMod q)) (Nat.zero_le L) hLU.le
    have hinterval (N : ℕ) : Finset.Ioc 0 N = Finset.Icc 1 N := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    simp only [hinterval] at hsplit
    have heq : ∑ P ∈ Finset.Ioc L (b / m), (primeWeight P : ℂ) * χ (P : ZMod q) =
        ∑ P ∈ Finset.Icc 1 (b / m), (primeWeight P : ℂ) * χ (P : ZMod q) -
          ∑ P ∈ Finset.Icc 1 L, (primeWeight P : ℂ) * χ (P : ZMod q) := by
      linear_combination hsplit
    have hmono : (q : ℝ) * (K * ((b : ℝ) / m) / Real.log ((b : ℝ) / m) ^ (2 * A + 1)) ≤
        (q : ℝ) * (K * ((b : ℝ) / m) / (c * Real.log X) ^ (2 * A + 1)) := by
      have hcl : 0 < c * Real.log X := mul_pos hc hlog0
      have hpow : (c * Real.log X) ^ (2 * A + 1) ≤ Real.log ((b : ℝ) / m) ^ (2 * A + 1) :=
        Real.rpow_le_rpow hcl.le hlogX' (by linarith)
      have hpos : 0 < (c * Real.log X) ^ (2 * A + 1) := Real.rpow_pos_of_pos hcl _
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg q)
      exact div_le_div_of_nonneg_left
        (mul_nonneg hK.le (div_nonneg (Nat.cast_nonneg b) hm0.le)) hpos hpow
    rw [heq]
    calc _ ≤ ‖∑ P ∈ Finset.Icc 1 (b / m), (primeWeight P : ℂ) * χ (P : ZMod q)‖ +
          ‖∑ P ∈ Finset.Icc 1 L, (primeWeight P : ℂ) * χ (P : ZMod q)‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  · rw [Finset.Ioc_eq_empty hLU, Finset.sum_empty, norm_zero]
    have hcl : 0 < c * Real.log X := mul_pos hc hlog0
    have hpos : 0 < (c * Real.log X) ^ (2 * A + 1) := Real.rpow_pos_of_pos hcl _
    refine mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg q) (div_nonneg ?_ hpos.le))
    exact mul_nonneg hK.le (div_nonneg (Nat.cast_nonneg b) hm0.le)

/-- P0069 page 51 display 5.17, the Siegel Walfisz estimate inside one rough variable.
For a nonprincipal character of modulus at most a log power of the scale `X`, the character
sum over integers in `(a, b]` with no prime factor below `z`, where `z ≥ X ^ c` and `b ≤ X`,
saves an arbitrary log power. Proof route: split each such integer as its largest prime factor
times a cofactor and apply the prime estimate in the largest prime factor. -/
theorem rough_character_interval {c : ℝ} (hc : 0 < c) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ A →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
        ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
          ‖∑ n ∈ Finset.Ioc a b, ((Task308.roughIndicator n z : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤
            C * b * Real.log X ^ (-A) := by
  obtain ⟨B, hB, K, hK, hpre⟩ := Prime514.character_prime_prefix_bound (2 * A + 1) (by linarith)
  have h1 := (isLittleO_log_rpow_rpow_atTop (A + B) (half_pos hc)).bound one_pos
  have h2 := (tendsto_rpow_atTop hc).eventually_ge_atTop 2
  obtain ⟨C1, hC1⟩ := Filter.eventually_atTop.mp (h1.and h2)
  have hcD : 0 < c ^ (2 * A + 1) := Real.rpow_pos_of_pos hc _
  have hC3 : (3 : ℝ) ≤ max C1 3 := le_max_right _ _
  have hK4 : 0 < 4 * K / c ^ (2 * A + 1) := by positivity
  refine ⟨max C1 3 + 4 * K / c ^ (2 * A + 1), by linarith, ?_⟩
  intro X hX q hq hqA χ hχ z hz a b ha hb
  have hX3 : 3 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hXC1 : C1 ≤ X := (le_max_left C1 3).trans (by linarith)
  obtain ⟨hlp1, hXc1⟩ := hC1 X hXC1
  have hlp0 : ‖Real.log X ^ (A + B)‖ ≤ 1 * ‖X ^ (c / 2)‖ := hlp1
  have hXc : 2 ≤ X ^ c := hXc1
  have hlog1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    exact (Real.exp_one_lt_three.le).trans hX3
  have hlog0 : 0 < Real.log X := by linarith
  have hlp : Real.log X ^ (A + B) ≤ X ^ (c / 2) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hlog0 _),
      abs_of_pos (Real.rpow_pos_of_pos hX0 _), one_mul] at hlp0
    exact hlp0
  have hz1 : 1 ≤ z := by
    have : (1 : ℝ) ≤ (z : ℝ) := by linarith
    exact_mod_cast this
  rw [rough_sum_reindex χ z a b ha hz1]
  have hcl : 0 < c * Real.log X := mul_pos hc hlog0
  have hpos : 0 < (c * Real.log X) ^ (2 * A + 1) := Real.rpow_pos_of_pos hcl _
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hterm : ∀ m ∈ Finset.Icc 1 b,
      ‖((Task308.roughIndicator m z : ℝ) : ℂ) * χ (m : ZMod q) *
        ∑ P ∈ Finset.Ioc (max (a / m) (max z (m.primeFactors.sup id) - 1)) (b / m),
          (primeWeight P : ℂ) * χ (P : ZMod q)‖ ≤
      2 * ((q : ℝ) * K * b / (c * Real.log X) ^ (2 * A + 1)) * (m : ℝ)⁻¹ := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hin := inner_prime_bound hc hB hpre hK hA hX3 hXc hlp hq hqA χ hχ hz hb hm1
      (max (a / m) (max z (m.primeFactors.sup id) - 1)) (by omega)
    have hr : ‖((Task308.roughIndicator m z : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real]
      unfold Task308.roughIndicator
      split_ifs <;> simp
    have hχ1 : ‖χ (m : ZMod q)‖ ≤ 1 := χ.norm_le_one _
    rw [norm_mul, norm_mul]
    calc _ ≤ 1 * 1 * (2 * ((q : ℝ) * (K * ((b : ℝ) / m) /
            (c * Real.log X) ^ (2 * A + 1)))) :=
          mul_le_mul (mul_le_mul hr hχ1 (norm_nonneg _) zero_le_one) hin (norm_nonneg _)
            (by norm_num)
      _ = _ := by ring
  have hharm : ∑ m ∈ Finset.Icc 1 b, (m : ℝ)⁻¹ ≤ 2 * Real.log X := by
    have h := harmonic_le_one_add_log b
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    have hlb : Real.log (b : ℝ) ≤ Real.log X := by
      rcases Nat.eq_zero_or_pos b with h0 | h0
      · rw [h0]
        simp only [Nat.cast_zero, Real.log_zero]
        exact hlog0.le
      · exact Real.log_le_log (by exact_mod_cast h0) hb
    linarith
  have hqK : 0 ≤ 2 * ((q : ℝ) * K * b / (c * Real.log X) ^ (2 * A + 1)) :=
    mul_nonneg (by norm_num)
      (div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg q) hK.le) hb0) hpos.le)
  have hpow1 : (c * Real.log X) ^ (2 * A + 1) =
      c ^ (2 * A + 1) * (Real.log X ^ A * Real.log X ^ A * Real.log X) := by
    rw [Real.mul_rpow hc.le hlog0.le, show 2 * A + 1 = A + A + 1 by ring,
      Real.rpow_add hlog0, Real.rpow_add hlog0, Real.rpow_one]
  have hl : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hlog0 _
  calc _ ≤ ∑ m ∈ Finset.Icc 1 b,
        2 * ((q : ℝ) * K * b / (c * Real.log X) ^ (2 * A + 1)) * (m : ℝ)⁻¹ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = 2 * ((q : ℝ) * K * b / (c * Real.log X) ^ (2 * A + 1)) *
        ∑ m ∈ Finset.Icc 1 b, (m : ℝ)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ 2 * ((q : ℝ) * K * b / (c * Real.log X) ^ (2 * A + 1)) * (2 * Real.log X) :=
        mul_le_mul_of_nonneg_left hharm hqK
    _ ≤ 2 * (Real.log X ^ A * K * b / (c * Real.log X) ^ (2 * A + 1)) * (2 * Real.log X) := by
        have hstep : (q : ℝ) * K * b / (c * Real.log X) ^ (2 * A + 1) ≤
            Real.log X ^ A * K * b / (c * Real.log X) ^ (2 * A + 1) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hqA hK.le) hb0) hpos.le
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hstep (by norm_num)) (by linarith)
    _ = 4 * K / c ^ (2 * A + 1) * b * Real.log X ^ (-A) := by
        rw [hpow1, Real.rpow_neg hlog0.le]
        have hl' : Real.log X ^ A ≠ 0 := hl.ne'
        have hlog' : Real.log X ≠ 0 := hlog0.ne'
        have hcD' : c ^ (2 * A + 1) ≠ 0 := hcD.ne'
        first
          | (field_simp; ring)
          | field_simp
    _ ≤ (max C1 3 + 4 * K / c ^ (2 * A + 1)) * b * Real.log X ^ (-A) := by
        have hn : 0 ≤ Real.log X ^ (-A) := Real.rpow_nonneg hlog0.le _
        have : 4 * K / c ^ (2 * A + 1) ≤ max C1 3 + 4 * K / c ^ (2 * A + 1) := by linarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hb0) hn

end LeanLab.BHP1997.Rough514
