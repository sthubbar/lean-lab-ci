/-
Cai 2002 page 601 and BJS page 4. Uniform dimension products.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.AlmostPrimeSums.Decomp1527c
import LeanLab.ChenExplicit.LinearSieve
open Filter Real Finset
open scoped Topology
namespace LeanLab.Cai2002
/-- A positive product limit gives the uniform dimension ratio away from a fixed initial segment.
Derived limiting step for Theorem 6 page 4 equation 4. -/
theorem dimension_ratio306 (V : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hV : ∀ x : ℝ, 2 ≤ x → 0 < V x)
    (hlim : Tendsto (fun x : ℝ => V x * log x / c) atTop (𝓝 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ w : ℝ, 3 ≤ w ∧ ∀ u z : ℝ, w ≤ u → u < z →
      V u / V z < (1 + ε) * (log z / log u) := by
  let η := ε / (2 * (ε + 2))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηsmall : η < 1 := by
    dsimp [η]
    apply (div_lt_one (by positivity)).mpr
    linarith
  have hηeq : η * (2 * (ε + 2)) = ε := by
    dsimp [η]
    field_simp
  have hcoeff : 1 + η < (1 + ε) * (1 - η) := by nlinarith
  obtain ⟨w0, hw0⟩ := eventually_atTop.mp
    ((hlim.eventually (eventually_lt_nhds (by linarith : (1 : ℝ) < 1 + η))).and
      (hlim.eventually (eventually_gt_nhds (by linarith : (1 : ℝ) - η < 1))))
  refine ⟨max w0 3, le_max_right _ _, fun u z hu huz => ?_⟩
  have hu0 : w0 ≤ u := (le_max_left ..).trans hu
  have hz0 : w0 ≤ z := hu0.trans huz.le
  have hu3 : 3 ≤ u := (le_max_right ..).trans hu
  have hz3 : 3 ≤ z := hu3.trans huz.le
  have hlu : 0 < log u := log_pos (by linarith)
  have hlz : 0 < log z := log_pos (by linarith)
  have hup := (div_lt_iff₀ hc).mp (hw0 u hu0).1
  have hlow := (lt_div_iff₀ hc).mp (hw0 z hz0).2
  have hprod : V u * log u < (1 + ε) * (V z * log z) := by
    have h1 : c * (1 + η) < c * ((1 + ε) * (1 - η)) :=
      mul_lt_mul_of_pos_left hcoeff hc
    have h2 := mul_lt_mul_of_pos_left hlow (show 0 < 1 + ε by linarith)
    nlinarith
  rw [div_lt_iff₀ (hV z (by linarith))]
  rw [show (1 + ε) * (log z / log u) * V z =
    ((1 + ε) * (V z * log z)) / log u by ring]
  exact (lt_div_iff₀ hlu).mpr hprod


/-- Odd primes strictly below a real cutoff. Theorem 6 page 4 equation 4. -/
noncomputable def oddSievePrimes306 (z : ℝ) : Finset ℕ :=
  (range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ 2 < p)

/-- The odd reciprocal totient sieve product. Cai page 601 equation 4.3. -/
noncomputable def oddSieveProduct306 (z : ℝ) : ℝ :=
  ∏ p ∈ oddSievePrimes306 z, (1 - 1 / ((p : ℝ) - 1))

/-- Every factor in the odd sieve product is strictly positive and at most one.
Cai page 601 equation 4.3. -/
theorem oddSieveFactor_bounds306 (p : ℕ) (hp : 2 < p) :
    0 < 1 - 1 / ((p : ℝ) - 1) ∧ 1 - 1 / ((p : ℝ) - 1) ≤ 1 := by
  have hpR : (2 : ℝ) < p := by exact_mod_cast hp
  constructor
  · apply sub_pos.mpr
    exact (div_lt_one (by linarith)).mpr (by linarith)
  · exact sub_le_self _ (div_nonneg zero_le_one (by linarith))

/-- Every finite odd sieve product is positive. Cai page 601 equation 4.3. -/
theorem oddSieveProduct_pos306 (z : ℝ) : 0 < oddSieveProduct306 z := by
  apply prod_pos
  intro p hp
  exact (oddSieveFactor_bounds306 p (mem_filter.mp hp).2.2).1

/-- The normalized full odd product tends to one.
Cai page 601 equation 4.3 before removing divisors of N. -/
theorem oddSieveProduct_limit306 :
    Tendsto (fun z : ℝ => oddSieveProduct306 z * log z /
      (2 * exp (-eulerMascheroniConstant) * LeanLab.ChenExplicit.twinC)) atTop (𝓝 1) := by
  exact LeanLab.AlmostPrimeSums.Decomp1527c.chen_odd_product_limit_of_mertens
    LeanLab.AlmostPrimeSums.Decomp1527c.mertens_euler_product

/-- The exact ratio of full odd products gives the interval product.
Theorem 6 page 4 equation 4. -/
theorem oddSieveProduct_ratio306 (u z : ℝ) (huz : u ≤ z) :
    (∏ p ∈ (oddSievePrimes306 z).filter (fun p : ℕ => u ≤ (p : ℝ)),
      (1 - 1 / ((p : ℝ) - 1))⁻¹) = oddSieveProduct306 u / oddSieveProduct306 z := by
  classical
  have hsub : oddSievePrimes306 u ⊆ oddSievePrimes306 z := by
    intro p hp
    obtain ⟨hpu, hpP⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hpu).trans_le (Nat.ceil_mono huz)), hpP⟩
  have hset : (oddSievePrimes306 z).filter (fun p : ℕ => u ≤ (p : ℝ)) =
      oddSievePrimes306 z \ oddSievePrimes306 u := by
    apply Finset.ext
    intro p
    rw [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hpz, hup⟩
      refine ⟨hpz, fun hpu => ?_⟩
      have hpu' := Finset.mem_range.mp (Finset.mem_filter.mp hpu).1
      exact (not_lt_of_ge hup) (Nat.lt_ceil.mp hpu')
    · rintro ⟨hpz, hpu⟩
      refine ⟨hpz, ?_⟩
      by_contra hh
      apply hpu
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (Nat.lt_ceil.mpr (lt_of_not_ge hh)), (Finset.mem_filter.mp hpz).2⟩
  rw [hset, prod_inv_distrib]
  have hid := prod_sdiff (f := fun p : ℕ => 1 - 1 / ((p : ℝ) - 1)) hsub
  change (∏ p ∈ oddSievePrimes306 z \ oddSievePrimes306 u,
    (1 - 1 / ((p : ℝ) - 1))) * oddSieveProduct306 u = oddSieveProduct306 z at hid
  apply (eq_div_iff (oddSieveProduct_pos306 z).ne').mpr
  rw [← hid]
  have hdiff : (∏ p ∈ oddSievePrimes306 z \ oddSievePrimes306 u,
      (1 - 1 / ((p : ℝ) - 1))) ≠ 0 := by
    apply ne_of_gt
    apply prod_pos
    intro p hp
    exact (oddSieveFactor_bounds306 p (mem_filter.mp (Finset.mem_sdiff.mp hp).1).2.2).1
  field_simp

/-- A fixed initial cutoff gives arbitrarily small dimension error for the full odd sieve.
Theorem 6 page 4 equation 4. -/
theorem oddSieve_dimension306 (ε : ℝ) (hε : 0 < ε) :
    ∃ w : ℝ, 3 ≤ w ∧ ∀ u z : ℝ, w ≤ u → u < z →
      (∏ p ∈ (oddSievePrimes306 z).filter (fun p : ℕ => u ≤ (p : ℝ)),
        (1 - 1 / ((p : ℝ) - 1))⁻¹) < (1 + ε) * (log z / log u) := by
  have hc : 0 < 2 * exp (-eulerMascheroniConstant) * LeanLab.ChenExplicit.twinC :=
    mul_pos (by positivity) LeanLab.ChenExplicit.twinC_pos
  obtain ⟨w, hw, hratio⟩ := dimension_ratio306 oddSieveProduct306 _ hc
    (fun x _ => oddSieveProduct_pos306 x) oddSieveProduct_limit306 ε hε
  refine ⟨w, hw, fun u z hu huz => ?_⟩
  rw [oddSieveProduct_ratio306 u z huz.le]
  exact hratio u z hu huz

/-- Deleting a fixed initial set of primes verifies the dimension condition uniformly
for every subset of the odd primes. Theorem 6 page 4 equation 4. -/
theorem sieve_dimension306 (ε : ℝ) (hε : 0 < ε) :
    ∃ w : ℝ, 3 ≤ w ∧ ∀ (P : Set ℕ), (∀ p ∈ P, p.Prime ∧ 2 < p) →
      ∀ z : ℝ, w < z → ∀ u : ℝ, 1 < u → u < z →
        (∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter
          (fun p : ℕ => p ∉ LeanLab.ChenExplicit.primesBelowIn P w ∧ u ≤ (p : ℝ)),
          (1 - 1 / ((p : ℝ) - 1))⁻¹) < (1 + ε) * (log z / log u) := by
  classical
  obtain ⟨w, hw, hd⟩ := oddSieve_dimension306 ε hε
  refine ⟨w, hw, fun P hP z hwz u hu huz => ?_⟩
  let v : ℝ := max u w
  have hvz : v < z := max_lt huz hwz
  have hwv : w ≤ v := le_max_right _ _
  have huv : u ≤ v := le_max_left _ _
  have hsub : (LeanLab.ChenExplicit.primesBelowIn P z).filter
      (fun p : ℕ => p ∉ LeanLab.ChenExplicit.primesBelowIn P w ∧ u ≤ (p : ℝ)) ⊆
      (oddSievePrimes306 z).filter (fun p : ℕ => v ≤ (p : ℝ)) := by
    intro p hp
    obtain ⟨hpz, hpw, hpu⟩ := mem_filter.mp hp
    obtain ⟨hpz', hpP⟩ := mem_filter.mp hpz
    have hwp : w ≤ (p : ℝ) := by
      by_contra h
      apply hpw
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_ceil.mpr (lt_of_not_ge h)), hpP⟩
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hpz', hP p hpP⟩, max_le hpu hwp⟩
  have hprod : (∏ p ∈ (LeanLab.ChenExplicit.primesBelowIn P z).filter
      (fun p : ℕ => p ∉ LeanLab.ChenExplicit.primesBelowIn P w ∧ u ≤ (p : ℝ)),
      (1 - 1 / ((p : ℝ) - 1))⁻¹) ≤
      ∏ p ∈ (oddSievePrimes306 z).filter (fun p : ℕ => v ≤ (p : ℝ)),
        (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
    apply Finset.prod_le_prod_of_subset_of_one_le₀ hsub
    · intro p hp
      have hb := oddSieveFactor_bounds306 p (hP p (mem_filter.mp (mem_filter.mp hp).1).2).2
      exact (inv_pos.mpr hb.1).le
    · intro p hp _
      have hb := oddSieveFactor_bounds306 p (mem_filter.mp (mem_filter.mp hp).1).2.2
      exact (one_le_inv₀ hb.1).mpr hb.2
  have hlog : log z / log v ≤ log z / log u :=
    div_le_div_of_nonneg_left (log_nonneg (by linarith)) (log_pos hu)
      (log_le_log (by linarith) huv)
  exact (hprod.trans_lt (hd v z hwv hvz)).trans_le
    (mul_le_mul_of_nonneg_left hlog (by linarith))

/-- The product of removed primes is bounded independently of the chosen odd prime subset.
Theorem 6 page 5 equation 10. -/
theorem sieve_exceptional_product306 (w : ℝ) (P : Set ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 2 < p) :
    (∏ q ∈ LeanLab.ChenExplicit.primesBelowIn P w, (q : ℝ)) ≤
      ∏ q ∈ oddSievePrimes306 w, (q : ℝ) := by
  classical
  have hsub : LeanLab.ChenExplicit.primesBelowIn P w ⊆ oddSievePrimes306 w := by
    intro p hp
    obtain ⟨hpw, hpP⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hpw, hP p hpP⟩
  apply Finset.prod_le_prod_of_subset_of_one_le₀ hsub
  · intro p _
    exact Nat.cast_nonneg _
  · intro p hp _
    have hh := (mem_filter.mp hp).2.1.one_lt.le
    exact_mod_cast hh

/-- The exact Q times D divisor remainder is dominated by the full coprime modulus sum
whenever its cutoff is within the distribution level. Cai page 601 equation 4.2 and
Theorem 6 page 5 equation 10. No factor Q is discarded. -/
theorem sieve_divisor_remainder306 (N : ℕ) (P : Set ℕ)
    (hP : ∀ p ∈ P, p.Coprime N) (z : ℝ) (Q : Finset ℕ) (D L : ℝ)
    (hcut : (∏ q ∈ Q, (q : ℝ)) * D ≤ L)
    (R : ℕ → ℝ) (hR : ∀ d : ℕ, 0 ≤ R d) :
    (∑ d ∈ (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p).divisors.filter
      (fun d : ℕ => (d : ℝ) < (∏ q ∈ Q, (q : ℝ)) * D), R d) ≤
      ∑ d ∈ (Icc 1 ⌊L⌋₊).filter (fun d => N.Coprime d), R d := by
  classical
  have hc : N.Coprime (∏ p ∈ LeanLab.ChenExplicit.primesBelowIn P z, p) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro p hp
    exact (hP p (mem_filter.mp hp).2).symm
  apply sum_le_sum_of_subset_of_nonneg _ (fun d _ _ => hR d)
  intro d hd
  obtain ⟨hdiv, hbound⟩ := mem_filter.mp hd
  have hdpos := Nat.pos_of_mem_divisors hdiv
  have hdvd := (Nat.mem_divisors.mp hdiv).1
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hdpos, Nat.le_floor (hbound.le.trans hcut)⟩,
    hc.coprime_dvd_right hdvd⟩

#print axioms sieve_divisor_remainder306

example : oddSievePrimes306 4 = {3} := by
  norm_num only [oddSievePrimes306, Nat.ceil_ofNat]
  decide

example : oddSieveProduct306 4 = 1 / 2 := by
  have hs : oddSievePrimes306 4 = {3} := by
    norm_num only [oddSievePrimes306, Nat.ceil_ofNat]
    decide
  rw [oddSieveProduct306, hs]
  norm_num

#print axioms sieve_exceptional_product306

#print axioms oddSieve_dimension306
#print axioms sieve_dimension306

#print axioms dimension_ratio306
#print axioms oddSieveFactor_bounds306
#print axioms oddSieveProduct_pos306
#print axioms oddSieveProduct_limit306
#print axioms oddSieveProduct_ratio306
end LeanLab.Cai2002
