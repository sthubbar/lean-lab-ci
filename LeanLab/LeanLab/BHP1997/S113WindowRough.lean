/-
Burst 2026-11-22, BHP1997, session S113, step window-s113. Split of the LEAF
`DQ517Window.leaf_rough_window_density` of `DQ517WindowLeaves`, P0069 Baker Harman Pintz 1997,
page 51, display 5.17: "a straightforward consequence of the prime number theorem, with error
term `Y exp(-ε L^(1/2))`", applied to the rough cofactor `n3` or `n5` of display 5.15, page 50.

The cut is the one of the proved log power route `RoughDensity517e`: the Buchstab recursion over
the least prime factor `p ≥ z` has three inputs, two of them left as LEAFs, each now stated with the error of 5.17,
`b exp(-N (log X)^(1/3))`:
* `leaf_prime_weight_transfer_window`, the prime number theorem in the least prime `p`, HARD in
  form but cited: it is partial summation against `DQ517StrongPNTInput.psi_error_stretched`;
* the integral equation of `ω` in summed form, PROVED in `S113WindowTelescope` as
  `leaf_buchstab_telescope_window_s113`, its error is a power saving `b / z`;
* `leaf_lattice_abel_window`, the lattice half of the Buchstab identity, MEDIUM.

PROVED here from the two leaves: `buchstab_main_term_window`, `rough_density_strip_window`, the
induction on the number of prime factors with `N + 1` absorbing the harmonic sum `2 log X`, and
`leaf_rough_window_density_s113`, with exactly the statement of
`DQ517Window.leaf_rough_window_density`, to be wired by the lab gate.

No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.RoughDensity517e
import LeanLab.BHP1997.S113WindowTelescope

namespace LeanLab.BHP1997.S113WindowRough
open Classical
open scoped BigOperators
open LeanLab.BHP1997.Task308 (roughIndicator)
open LeanLab.BHP1997.LowerShortC165 (rough_sum_decomp cofactor_one_split)

/-- LEAF: page 51 display 5.17, the prime number theorem applied to the least prime factor
`p ≥ z` in the Buchstab recursion for the rough cofactor of display 5.15. HARD. The sum over
primes `p ≥ z` of `[a < p] + ∑_{a/p < m ≤ b/p, m > 1} ω(log m / log p) / log p` is the sum over
all integers `k ≥ z` of the same weight over `log k`, with the error `b exp(-N (log X)^(1/3))`
of 5.17. Window form of `LowerShortC165.prime_weight_transfer`; route:
`LowerShortC165.prime_transfer_abstract` with the prime count input from
`DQ517StrongPNTInput.psi_error_stretched` at every level `Y ≥ X ^ c`. -/
theorem leaf_prime_weight_transfer_window (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
            ((if a < p then (1 : ℝ) else 0) +
              ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
                ω (Real.log m / Real.log p) / Real.log p) -
          ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
            ((if a < k then (1 : ℝ) else 0) +
              ∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k),
                ω (Real.log m / Real.log k) / Real.log k) / Real.log k| ≤
          C * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  sorry

/-- LEAF: page 51 display 5.17, the lattice half of the Buchstab identity for densities, for
the rough cofactor of display 5.15. MEDIUM. The sum over `n` in `(a, b]` and levels `z ≤ k < n`
of `ω(log (n / k) / log k) / (k log^2 k)` is the sum over levels `k ≥ z` of the Buchstab density
sums at level `k` over the cofactors `m` in `(a / k, b / k]`, divided by `log k`, with the error
`b exp(-N (log X)^(1/3))` of 5.17. Window form of `LowerShortC165.lattice_abel`. -/
theorem leaf_lattice_abel_window (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ n ∈ Finset.Ioc a b, ∑ k ∈ Finset.Ico z n,
            ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) -
          ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
            (∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k),
              ω (Real.log m / Real.log k) / Real.log k) / Real.log k| ≤
          C * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  sorry

/-! ### Proved steps -/

/-- Page 51 display 5.17, the error bookkeeping of the induction: one more unit of `N` absorbs
the harmonic sum `2 log X`, since `log X = l ^ 3 ≤ 6 e ^ l` with `l = (log X)^(1/3)`. -/
theorem exp_step_absorb {X : ℝ} (hX : 1 ≤ X) (N : ℝ) :
    Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)) * (2 * Real.log X) ≤
      12 * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  have hlx : 0 ≤ Real.log X := Real.log_nonneg hX
  set l := Real.log X ^ (1 / 3 : ℝ) with hl
  have hl0 : 0 ≤ l := Real.rpow_nonneg hlx _
  have hl3 : l ^ 3 = Real.log X := by
    rw [hl, ← Real.rpow_natCast, ← Real.rpow_mul hlx]
    norm_num
  have h2 := Real.pow_div_factorial_le_exp l hl0 3
  have hfac : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hfac] at h2
  have hsplit : Real.exp (-(N + 1) * l) = Real.exp (-N * l) * Real.exp (-l) := by
    rw [← Real.exp_add]; ring_nf
  have hel : Real.exp (-l) * Real.exp l = 1 := by rw [← Real.exp_add]; simp
  have hE0 : 0 < Real.exp (-N * l) := Real.exp_pos _
  have hm0 : 0 < Real.exp (-l) := Real.exp_pos _
  rw [hsplit, ← hl3]
  have key : Real.exp (-l) * (2 * l ^ 3) ≤ 12 := by
    have : l ^ 3 ≤ 6 * Real.exp l := by linarith [(div_le_iff₀ (by norm_num : (0:ℝ) < 6)).mp h2]
    nlinarith
  calc Real.exp (-N * l) * Real.exp (-l) * (2 * l ^ 3)
      = Real.exp (-N * l) * (Real.exp (-l) * (2 * l ^ 3)) := by ring
    _ ≤ Real.exp (-N * l) * 12 := mul_le_mul_of_nonneg_left key hE0.le
    _ = 12 * Real.exp (-N * l) := by ring

/-- PROVED from the two leaves of this file: page 51 display 5.17, the Buchstab recursion for
the main terms alone, the window form of `LowerShortC165.buchstab_main_term`. -/
theorem buchstab_main_term_window (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log z) / Real.log z -
          ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
            ((if a < p then (1 : ℝ) else 0) +
              ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
                ω (Real.log m / Real.log p) / Real.log p)| ≤
          C * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  obtain ⟨CA, hCA, hA'⟩ := leaf_prime_weight_transfer_window ω hω hz hc N hN
  obtain ⟨C1, hC1, h1'⟩ := S113WindowTelescope.leaf_buchstab_telescope_window_s113 ω hω hz hc N hN
  obtain ⟨C2, hC2, h2'⟩ := leaf_lattice_abel_window ω hω hz hc N hN
  refine ⟨CA + C1 + C2, by positivity, fun X hX z hzX a b ha hb => ?_⟩
  have hAb := hA' X (by linarith) z hzX a b ha hb
  have h1 := h1' X (by linarith) z hzX a b ha hb
  have h2 := h2' X (by linarith) z hzX a b ha hb
  have hid : ∑ n ∈ Finset.Ioc a b, (if z ≤ n then 1 / Real.log (n : ℝ) else 0) =
      ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
        (if a < k then (1 : ℝ) else 0) / Real.log k := by
    have hI : Finset.Ioc a b = (Finset.Icc 1 b).filter (fun k => a < k) := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hI, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : a < k <;> by_cases h2 : z ≤ k <;> simp [h1, h2]
  have e1 : ∑ n ∈ Finset.Ioc a b, ((if z ≤ n then 1 / Real.log (n : ℝ) else 0) +
        ∑ k ∈ Finset.Ico z n, ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2)) =
      ∑ n ∈ Finset.Ioc a b, (if z ≤ n then 1 / Real.log (n : ℝ) else 0) +
        ∑ n ∈ Finset.Ioc a b, ∑ k ∈ Finset.Ico z n,
          ω (Real.log n / Real.log k - 1) / (k * Real.log k ^ 2) := Finset.sum_add_distrib
  have e2 : ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
        ((if a < k then (1 : ℝ) else 0) +
          ∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k),
            ω (Real.log m / Real.log k) / Real.log k) / Real.log k =
      ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
          (if a < k then (1 : ℝ) else 0) / Real.log k +
        ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
          (∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k),
            ω (Real.log m / Real.log k) / Real.log k) / Real.log k := by
    simp only [add_div, Finset.sum_add_distrib]
  rw [e1, hid] at h1
  rw [e2] at hAb
  obtain ⟨hA1, hA2⟩ := abs_le.mp hAb
  obtain ⟨h11, h12⟩ := abs_le.mp h1
  obtain ⟨h21, h22⟩ := abs_le.mp h2
  rw [abs_le]
  constructor <;> linarith

/-- PROVED from the two leaves of this file: page 51 display 5.17, the induction on the
number of prime factors of the rough cofactor, window form of
`LowerShortC165.rough_density_strip`. -/
theorem rough_density_strip_window (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (k : ℕ) : ∀ N : ℝ, 0 < N →
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X → b < z ^ (k + 1) →
        |∑ n ∈ Finset.Ioc a b, (roughIndicator n z -
            ω (Real.log n / Real.log z) / Real.log z)| ≤
          C * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  induction k with
  | zero =>
    intro N hN
    refine ⟨1, one_pos, fun X hX z _ a b ha _ hbz => ?_⟩
    rw [zero_add, pow_one] at hbz
    have hzero : ∑ n ∈ Finset.Ioc a b, (roughIndicator n z -
        ω (Real.log n / Real.log z) / Real.log z) = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      obtain ⟨hna, hnb⟩ := Finset.mem_Ioc.mp hn
      have hnz : n < z := lt_of_le_of_lt hnb hbz
      have hr : roughIndicator n z = 0 := by
        unfold roughIndicator
        rw [ite_eq_right]
        rintro (h | h)
        · omega
        · have := Nat.minFac_le (by omega : 0 < n)
          omega
      have hlz : 0 < Real.log z := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
      have hu : Real.log n / Real.log z < 1 := by
        rw [div_lt_one hlz]
        exact Real.log_lt_log (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hnz)
      rw [hr, hz _ hu]
      simp
    rw [hzero, abs_zero]
    have := (Real.exp_pos (-N * Real.log X ^ (1 / 3 : ℝ))).le
    positivity
  | succ k ih =>
    intro N hN
    obtain ⟨C1, hC1, h1⟩ := ih (N + 1) (by linarith)
    obtain ⟨C2, hC2, h2⟩ := buchstab_main_term_window ω hω hz hc N hN
    refine ⟨max (max C1 C2) 3 + 12 * C1 + C2, by positivity, fun X hX z hzX a b ha hb hbz => ?_⟩
    have hm3 : (3 : ℝ) ≤ max (max C1 C2) 3 := le_max_right _ _
    have hm1 : C1 ≤ max (max C1 C2) 3 := (le_max_left _ _).trans (le_max_left _ _)
    have hm2 : C2 ≤ max (max C1 C2) 3 := (le_max_right _ _).trans (le_max_left _ _)
    have hX1 : C1 ≤ X := by linarith
    have hX2 : C2 ≤ X := by linarith
    have hX3 : 3 ≤ X := by linarith
    have hlog1 : 1 ≤ Real.log X :=
      (Real.le_log_iff_exp_le (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])
    have hlog0 : 0 < Real.log X := by linarith
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    have habs := exp_step_absorb (by linarith : (1 : ℝ) ≤ X) N
    have hL0 : 0 ≤ Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)) := (Real.exp_pos _).le
    have hsplit : ∀ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
        ∑ m ∈ Finset.Ioc (a / p) (b / p), roughIndicator m p =
          (if a < p then (1 : ℝ) else 0) +
            ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p), roughIndicator m p := by
      intro p hp
      obtain ⟨hpI, hpp, -⟩ := Finset.mem_filter.mp hp
      rw [cofactor_one_split hpp.two_le (Finset.mem_Icc.mp hpI).2 (fun m => roughIndicator m p)]
      simp [roughIndicator]
    have key : ∑ n ∈ Finset.Ioc a b, (roughIndicator n z -
          ω (Real.log n / Real.log z) / Real.log z) =
        ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
          ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
            (roughIndicator m p - ω (Real.log m / Real.log p) / Real.log p) -
        (∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log z) / Real.log z -
          ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
            ((if a < p then (1 : ℝ) else 0) +
              ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
                ω (Real.log m / Real.log p) / Real.log p)) := by
      rw [Finset.sum_sub_distrib, rough_sum_decomp z a b ha, Finset.sum_congr rfl hsplit]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      ring
    have hinner : ∀ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
        |∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
            (roughIndicator m p - ω (Real.log m / Real.log p) / Real.log p)| ≤
          C1 * b * Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)) * (p : ℝ)⁻¹ := by
      intro p hp
      obtain ⟨hpI, hpp, hzp⟩ := Finset.mem_filter.mp hp
      have hp0 : 0 < p := hpp.pos
      have hbp : b / p < p ^ (k + 1) := by
        rw [Nat.div_lt_iff_lt_mul hp0, ← pow_succ]
        exact lt_of_lt_of_le hbz (Nat.pow_le_pow_left hzp _)
      have hcast : ((b / p : ℕ) : ℝ) ≤ (b : ℝ) / p := Nat.cast_div_le
      have hbpX : ((b / p : ℕ) : ℝ) ≤ X :=
        le_trans (by exact_mod_cast Nat.div_le_self b p) hb
      have h := h1 X hX1 p (hzX.trans (by exact_mod_cast hzp)) (max (a / p) 1) (b / p)
        (le_max_right _ _) hbpX hbp
      calc _ ≤ C1 * ((b / p : ℕ) : ℝ) * Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)) := h
        _ ≤ C1 * ((b : ℝ) / p) * Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)) := by gcongr
        _ = _ := by rw [div_eq_mul_inv]; ring
    have hharm : ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p), ((p : ℝ))⁻¹ ≤
        2 * Real.log X := by
      have hs : ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p), ((p : ℝ))⁻¹ ≤
          ∑ p ∈ Finset.Icc 1 b, ((p : ℝ))⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => by positivity)
      have hh : ∑ p ∈ Finset.Icc 1 b, ((p : ℝ))⁻¹ = (harmonic b : ℝ) := by
        simp [harmonic_eq_sum_Icc]
      have hl : Real.log b ≤ Real.log X := by
        rcases Nat.eq_zero_or_pos b with h0 | h0
        · subst h0
          simpa using hlog0.le
        · exact Real.log_le_log (by exact_mod_cast h0) hb
      have := harmonic_le_one_add_log b
      linarith
    have hleaf := h2 X hX2 z hzX a b ha hb
    rw [key]
    calc _ ≤ |∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
              ∑ m ∈ Finset.Ioc (max (a / p) 1) (b / p),
                (roughIndicator m p - ω (Real.log m / Real.log p) / Real.log p)| +
            C2 * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := (abs_sub _ _).trans (by gcongr)
      _ ≤ ∑ p ∈ (Finset.Icc 1 b).filter (fun p => p.Prime ∧ z ≤ p),
              C1 * b * Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)) * (p : ℝ)⁻¹ + C2 * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hinner)
      _ ≤ C1 * b * Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)) * (2 * Real.log X) + C2 * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
          rw [← Finset.mul_sum]
          gcongr
      _ = C1 * b * (Real.exp (-(N + 1) * Real.log X ^ (1 / 3 : ℝ)) * (2 * Real.log X)) + C2 * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by ring
      _ ≤ C1 * b * (12 * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ))) + C2 * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by gcongr
      _ = (12 * C1 + C2) * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by ring
      _ ≤ (max (max C1 C2) 3 + 12 * C1 + C2) * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
          have := (Real.exp_pos (-N * Real.log X ^ (1 / 3 : ℝ))).le
          gcongr
          linarith

/-- PROVED from the two leaves of this file: page 51 display 5.17 for the rough cofactor
`n3` or `n5` of display 5.15, with exactly the statement of the LEAF
`DQ517Window.leaf_rough_window_density` of `DQ517WindowLeaves`, to be wired by the lab gate. -/
theorem leaf_rough_window_density_s113 (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {c : ℝ} (hc : 0 < c) (N : ℝ) (hN : 0 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, C ≤ X → ∀ z : ℕ, X ^ c ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
        |∑ n ∈ Finset.Ioc a b, (Task308.roughIndicator n z -
            ω (Real.log n / Real.log z) / Real.log z)| ≤
          C * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
  obtain ⟨C, hC, h⟩ := rough_density_strip_window ω hω hz hc ⌈1 / c⌉₊ N hN
  refine ⟨C + 2, by linarith, fun X hX z hzX a b ha hb => ?_⟩
  have hX1 : 1 < X := by linarith
  have hk : 1 < c * ((⌈1 / c⌉₊ + 1 : ℕ) : ℝ) := by
    have h1 : 1 / c ≤ (⌈1 / c⌉₊ : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hc] at h1
    push_cast
    nlinarith
  have hbz : b < z ^ (⌈1 / c⌉₊ + 1) := by
    have h3 : X < (z : ℝ) ^ (⌈1 / c⌉₊ + 1) := by
      calc X = X ^ (1 : ℝ) := (Real.rpow_one X).symm
        _ < X ^ (c * ((⌈1 / c⌉₊ + 1 : ℕ) : ℝ)) := Real.rpow_lt_rpow_of_exponent_lt hX1 hk
        _ = (X ^ c) ^ (⌈1 / c⌉₊ + 1) := by
            rw [Real.rpow_mul (by linarith), Real.rpow_natCast]
        _ ≤ (z : ℝ) ^ (⌈1 / c⌉₊ + 1) :=
            pow_le_pow_left₀ (Real.rpow_nonneg (by linarith) _) hzX _
    exact_mod_cast lt_of_le_of_lt hb h3
  have hlog := (Real.exp_pos (-N * Real.log X ^ (1 / 3 : ℝ))).le
  calc _ ≤ C * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := h X (by linarith) z hzX a b ha hb hbz
    _ ≤ (C + 2) * b * Real.exp (-N * Real.log X ^ (1 / 3 : ℝ)) := by
        have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
        gcongr
        linarith

end LeanLab.BHP1997.S113WindowRough
