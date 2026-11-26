/-
The arithmetic denominator mass in P0013 page 45 equation 4.40.
These proofs do not establish Montgomery's prime supported operator inequality.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib
import LeanLab.PNTPort.BV.Helpers

namespace LeanLab.HelfgottArcs.SieveMass707
open Finset
open LeanLab.PNTPort.BV

/-- The reciprocal mass of integers supported on the prime factors of d is d over phi d.
Source: P0013 page 45 equation 4.40, an arithmetic input to Lemma 4.3. -/
theorem factored_reciprocal_hasSum707 (d : ℕ) (hd : 0 < d) :
    HasSum (fun m : Nat.factoredNumbers d.primeFactors => ((m : ℕ) : ℝ)⁻¹)
      ((d : ℝ) / d.totient) := by
  let f : ℕ →* ℝ :=
    { toFun := fun n => (n : ℝ)⁻¹
      map_one' := by simp
      map_mul' := by intros; simp [mul_inv_rev, mul_comm] }
  have hsmall {p : ℕ} (hp : p.Prime) : ‖f p‖ < 1 := by
    change ‖(p : ℝ)⁻¹‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have he := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    hsmall d.primeFactors).2
  have hfilter : {p ∈ d.primeFactors | p.Prime} = d.primeFactors := by
    apply filter_eq_self.mpr
    intro p hp
    exact Nat.prime_of_mem_primeFactors hp
  rw [hfilter] at he
  have hprod : (∏ p ∈ d.primeFactors, (1 - f p)⁻¹) = (d : ℝ) / d.totient := by
    have hphi : (d.totient : ℝ) = (d : ℝ) * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹) := by
      have hh := congrArg (fun z : ℚ => (z : ℝ)) (Nat.totient_eq_mul_prod_factors d)
      push_cast at hh
      exact hh
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    change (∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹) = _
    rw [prod_inv_distrib, hphi]
    simp [div_mul_eq_div_div, hd0]
  rw [hprod] at he
  exact he

example := factored_reciprocal_hasSum707 6 (by norm_num)

/-- A finite reciprocal mass with one fixed positive radical is at most inverse phi of that radical.
Source: P0013 page 45 equation 4.40, an arithmetic input to Lemma 4.3. -/
theorem radical_fiber_reciprocal707 (s : Finset ℕ) (d : ℕ) (hd : 0 < d)
    (hs : ∀ n ∈ s, n ≠ 0 ∧ UniqueFactorizationMonoid.radical n = d)
    :
    ∑ n ∈ s, (n : ℝ)⁻¹ ≤ 1 / (d.totient : ℝ) := by
  have hseries := factored_reciprocal_hasSum707 d hd
  have hdn (n : ℕ) (hn : n ∈ s) : d ∣ n := by
    rw [← (hs n hn).2]
    exact UniqueFactorizationMonoid.radical_dvd_self
  have hmem (n : ℕ) (hn : n ∈ s) : n / d ∈ Nat.factoredNumbers d.primeFactors := by
    apply Nat.mem_factoredNumbers_of_primeFactors_subset
    · exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (hs n hn).1) (hdn n hn)) hd)
    · have hh := Nat.primeFactors_mono (Nat.div_dvd_of_dvd (hdn n hn)) (hs n hn).1
      have heq : n.primeFactors = d.primeFactors := by
        rw [← (hs n hn).2, Nat.primeFactors_radical]
      rwa [heq] at hh
  let g : {n // n ∈ s} → Nat.factoredNumbers d.primeFactors := fun n => ⟨n.val / d, hmem n.val n.property⟩
  have hg : Function.Injective g := by
    intro n m he
    have he' := congrArg (fun k : Nat.factoredNumbers d.primeFactors => (k : ℕ)) he
    change n.val / d = m.val / d at he'
    apply Subtype.ext
    calc
      n.val = d * (n.val / d) := (Nat.mul_div_cancel' (hdn n.val n.property)).symm
      _ = d * (m.val / d) := by rw [he']
      _ = m.val := Nat.mul_div_cancel' (hdn m.val m.property)
  have hh := hasSum_le_inj g hg (fun _ _ => by positivity) (fun _ => le_rfl)
    (hasSum_fintype (fun n : {n // n ∈ s} => ((g n : ℕ) : ℝ)⁻¹)) hseries
  have heq : (∑ n : {n // n ∈ s}, ((g n : ℕ) : ℝ)⁻¹) =
      (d : ℝ) * ∑ n ∈ s, (n : ℝ)⁻¹ := by
    rw [Finset.sum_coe_sort_eq_attach]
    conv_rhs => rw [← Finset.sum_attach s (fun n : ℕ => (n : ℝ)⁻¹), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    change ((n.val / d : ℕ) : ℝ)⁻¹ = (d : ℝ) * (n.val : ℝ)⁻¹
    rw [Nat.cast_div (hdn n.val n.property) (by exact_mod_cast hd.ne'), inv_div]
    rfl
  rw [heq] at hh
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  apply le_of_mul_le_mul_left (a := (d : ℝ)) ?_ hd0
  simpa only [mul_one_div] using hh

example := radical_fiber_reciprocal707 {1} 1 (by norm_num) (by
  intro n hn
  have he : n = 1 := mem_singleton.mp hn
  subst n
  simp)

/-- The squarefree inverse totient mass through N dominates the harmonic sum through N.
Source: P0013 page 45 equation 4.40, an arithmetic input to Lemma 4.3. -/
theorem sieve_mass_harmonic707 (N : ℕ) :
    (harmonic N : ℝ) ≤ ∑ d ∈ Icc 1 N,
      (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2 / (d.totient : ℝ)) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  have hmaps : ∀ n ∈ Icc 1 N, UniqueFactorizationMonoid.radical n ∈ Icc 1 N := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
    exact mem_Icc.mpr ⟨Nat.radical_pos n, (Nat.radical_le_self_iff.mpr (by omega)).trans hnN⟩
  have hfib := sum_fiberwise_of_maps_to hmaps (fun n : ℕ => (n : ℝ)⁻¹)
  rw [← hfib]
  apply sum_le_sum
  intro d hd
  by_cases hsf : Squarefree d
  · have hmu : ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
    rw [hmu]
    apply radical_fiber_reciprocal707 _ d (by have := (mem_Icc.mp hd).1; omega)
    intro n hn
    obtain ⟨hn, he⟩ := mem_filter.mp hn
    exact ⟨by have := (mem_Icc.mp hn).1; omega, he⟩
  · have hempty : {n ∈ Icc 1 N | UniqueFactorizationMonoid.radical n = d} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro n hn
      have he := (mem_filter.mp hn).2
      exact hsf (he ▸ UniqueFactorizationMonoid.squarefree_radical)
    rw [hempty, sum_empty, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
    norm_num

example := sieve_mass_harmonic707 6

/-- A nonnegative multiplicative weight with squarefree support splits into a divisor of q and a part coprime to q.
Source: P0013 page 45 equation 4.40, an arithmetic input to Lemma 4.3. -/
theorem squarefree_coprime_mass_comparison707 (N q : ℕ) (hq : q ≠ 0) (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) (hnonneg : ∀ n, 0 ≤ f n)
    (hsupport : ∀ n, ¬ Squarefree n → f n = 0) :
    ∑ n ∈ Icc 1 N, f n ≤ (∑ d ∈ q.divisors, f d) *
      ∑ m ∈ (Icc 1 N).filter (fun m => m.Coprime q), f m := by
  let s := (Icc 1 N).filter Squarefree
  let t := q.divisors ×ˢ (Icc 1 N).filter (fun m => m.Coprime q)
  let g : ℕ → ℕ × ℕ := fun n => (n.gcd q, n / n.gcd q)
  have hmul (n : ℕ) : n.gcd q * (n / n.gcd q) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_left n q)
  have hmaps : ∀ n ∈ s, g n ∈ t := by
    intro n hn
    obtain ⟨hn, hsf⟩ := mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
    have hd0 : 0 < n.gcd q := Nat.gcd_pos_of_pos_right n (Nat.pos_of_ne_zero hq)
    have hk0 : 0 < n / n.gcd q :=
      Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left n q)) hd0
    apply mem_product.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n q, hq⟩, ?_⟩
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hk0, (Nat.div_le_self _ _).trans hnN⟩,
      Nat.coprime_div_gcd_of_squarefree hsf hq⟩
  have hinj : Set.InjOn g s := by
    intro n hn m hm he
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    change n.gcd q = m.gcd q at he1
    change n / n.gcd q = m / m.gcd q at he2
    calc
      n = n.gcd q * (n / n.gcd q) := (hmul n).symm
      _ = m.gcd q * (m / m.gcd q) := congrArg₂ (fun x y : ℕ => x * y) he1 he2
      _ = m := hmul m
  have hweight (n : ℕ) (hn : n ∈ s) : f n = f (g n).1 * f (g n).2 := by
    have hsf := (mem_filter.mp hn).2
    have hc := Nat.coprime_div_gcd_of_squarefree hsf hq
    have hc' : (n.gcd q).Coprime (n / n.gcd q) :=
      (hc.of_dvd_right (Nat.gcd_dvd_right n q)).symm
    simpa only [g, hmul n] using hf.map_mul_of_coprime hc'
  have heq : ∑ n ∈ Icc 1 N, f n = ∑ n ∈ s, f n := by
    symm
    apply sum_subset (filter_subset _ _)
    intro n hn hns
    apply hsupport
    intro hsf
    exact hns (mem_filter.mpr ⟨hn, hsf⟩)
  rw [heq, sum_mul_sum, ← sum_product']
  change (∑ n ∈ s, f n) ≤ ∑ z ∈ t, f z.1 * f z.2
  calc
    _ = ∑ n ∈ s, f (g n).1 * f (g n).2 := sum_congr rfl hweight
    _ = ∑ z ∈ s.image g, f z.1 * f z.2 := (sum_image (f := fun z : ℕ × ℕ => f z.1 * f z.2) hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg
      (fun z hz => by obtain ⟨n, hn, rfl⟩ := mem_image.mp hz; exact hmaps n hn)
      (fun z hz hnot => mul_nonneg (hnonneg _) (hnonneg _))

example := squarefree_coprime_mass_comparison707 10 6 (by norm_num)
  LeanLab.PNTPort.BV.sqfTot LeanLab.PNTPort.BV.sqfTot_mult LeanLab.PNTPort.BV.sqfTot_nonneg
  (by intro n hn; simp [LeanLab.PNTPort.BV.sqfTot_apply, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn])

/-- Restricting the squarefree inverse totient mass to coprime indices loses at most phi q over q.
Source: P0013 page 45 equation 4.40, an arithmetic input to Lemma 4.3. -/
theorem sieve_mass_coprime_comparison707 (N q : ℕ) (hq : 0 < q) :
    ((q.totient : ℝ) / q) * (∑ n ∈ Icc 1 N,
      (((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / (n.totient : ℝ))) ≤
      ∑ n ∈ (Icc 1 N).filter (fun n => n.Coprime q),
        (((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / (n.totient : ℝ)) := by
  change ((q.totient : ℝ) / q) * (∑ n ∈ Icc 1 N, sqfTot n) ≤
    ∑ n ∈ (Icc 1 N).filter (fun n => n.Coprime q), sqfTot n
  have hsupport (n : ℕ) (hn : ¬ Squarefree n) : sqfTot n = 0 := by
    simp [sqfTot_apply, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
  have hbound := squarefree_coprime_mass_comparison707 N q hq.ne' sqfTot
    sqfTot_mult sqfTot_nonneg hsupport
  have heq : ∑ d ∈ q.divisors, sqfTot d = (q : ℝ) / q.totient := by
    have hh := congrArg (fun f : ArithmeticFunction ℝ => f q) idTot_eq
    simpa only [idTot, ArithmeticFunction.coe_mk, ArithmeticFunction.coe_mul_zeta_apply] using hh.symm
  rw [heq] at hbound
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hphi : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  have hh := mul_le_mul_of_nonneg_left hbound (show 0 ≤ (q.totient : ℝ) / q by positivity)
  convert hh using 1
  field_simp

example := sieve_mass_coprime_comparison707 10 6 (by norm_num)

/-- The coprime squarefree inverse totient mass has the logarithmic lower bound used in equation 4.40.
Source: P0013 page 45 equation 4.40, an arithmetic input to Lemma 4.3. -/
theorem sieve_mass_coprime_log_lower707 (R : ℝ) (hR : 1 ≤ R) (q : ℕ) (hq : 0 < q) :
    ((q.totient : ℝ) / q) * Real.log R ≤
      ∑ n ∈ (Icc 1 ⌊R⌋₊).filter (fun n => n.Coprime q),
        (((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / (n.totient : ℝ)) := by
  have hh := (log_le_harmonic_floor R (by linarith)).trans
    (sieve_mass_harmonic707 ⌊R⌋₊)
  exact (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (q.totient : ℝ) / q)).trans
    (sieve_mass_coprime_comparison707 ⌊R⌋₊ q hq)

example := sieve_mass_coprime_log_lower707 10 (by norm_num) 6 (by norm_num)

/-- The arithmetic denominator at the inverse square root choice of R gives the final factor in equation 4.40.
Source: P0013 page 45 equation 4.40, an arithmetic input to Lemma 4.3. -/
theorem sieve_mass_prime_support_gain707 (q : ℕ) (hq : 0 < q) (t : ℝ)
    (ht : 0 < t) (hqt : (q : ℝ) * t ≤ 1) :
    (q.totient : ℝ) / (2 * q) * Real.log (((q : ℝ) * t)⁻¹) ≤
      ∑ n ∈ (Icc 1 ⌊1 / Real.sqrt ((q : ℝ) * t)⌋₊).filter (fun n => n.Coprime q),
        (((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ 2 / (n.totient : ℝ)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hz : 0 < (q : ℝ) * t := mul_pos hq0 ht
  have hs : 0 < Real.sqrt ((q : ℝ) * t) := Real.sqrt_pos.mpr hz
  have hs1 : Real.sqrt ((q : ℝ) * t) ≤ 1 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num, by simpa using hqt⟩
  have hR : 1 ≤ 1 / Real.sqrt ((q : ℝ) * t) := by
    apply (le_div_iff₀ hs).mpr
    simpa using hs1
  have hh := sieve_mass_coprime_log_lower707 (1 / Real.sqrt ((q : ℝ) * t)) hR q hq
  have hlog : Real.log (1 / Real.sqrt ((q : ℝ) * t)) =
      1 / 2 * Real.log (((q : ℝ) * t)⁻¹) := by
    rw [Real.log_div (by norm_num) hs.ne', Real.log_one, Real.log_sqrt hz.le, Real.log_inv]
    ring
  rw [hlog] at hh
  convert hh using 1
  ring

example := sieve_mass_prime_support_gain707 2 (by norm_num) (1 / 8) (by norm_num) (by norm_num)

end LeanLab.HelfgottArcs.SieveMass707
