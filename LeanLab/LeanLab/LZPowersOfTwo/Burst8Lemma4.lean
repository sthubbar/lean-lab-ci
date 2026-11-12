/-
ROUTE BURST session 8, part 2 of the LZPowersOfTwo split: Lemma 4 of P0079.
Paper: P0079 A. Languasco and A. Zaccagnini, "On a Diophantine problem with two primes and
s powers of two", arXiv 0811.3663v2, 2 Apr 2009, pages 5 to 7, displays (20) to (28).
AI wrote this Lean code. Binary Goldbach is OPEN; this file says nothing about it.

The session 4 leaf `Burst4Split.paired_second_moment_sharpB4` is proved here as
`paired_second_moment_p2`, with no sorry of its own, from two cited outside inputs and the prime number theorem:
* `chen_lemma3_p2`: Lemma 3 of the paper, Bombieri and Davenport Theorem 2 with Chen's
  constant `B = 3.9171`, page 6.
* `khalfalah_pintz_lemma1_p2`: Lemma 1 of the paper with the bound (22), page 5.
* `theta_pnt_p2`: the prime number theorem for `θ`, used for display (26); this one is
  PROVED from the lab port `LeanLab.PNTPort.StrongPNT.MediumPNT`, see `Burst8PNT.lean`.
Everything else, the Fourier identity (23), the lattice reduction (24) and (25), the
diagonal (26), the off-diagonal reduction (27) and the multiplicativity step before (28),
is PROVED below.
-/
import LeanLab.LZPowersOfTwo.Burst4Split
import LeanLab.LZPowersOfTwo.Burst8PNT

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo.Burst8P2

open LeanLab.LZPowersOfTwo LeanLab.LZPowersOfTwo.Burst4Split

/-! ### Definitions of page 5 -/

/-- P0079 page 4, the primes `εX ≤ p ≤ X` of the prime sum `S`. -/
abbrev boxP (ε X : ℝ) : Finset ℕ :=
  (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ))

/-- P0079 page 5, display (20): `Z(X; 2n) = ∑_{εX ≤ p ≤ X} ∑_{p' ≤ X, p' - p = 2n} log p log p'`. -/
def twinZ (ε X : ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ boxP ε X, ∑ p' ∈ (range (⌊X⌋₊ + 1)).filter (fun p' : ℕ => p'.Prime),
    if (p' : ℤ) - p = 2 * n then log p * log p' else 0

/-- P0079 page 5, display (21): `c0 = ∏_{p > 2} (1 - 1/(p-1)^2)`. -/
def twinC0 : ℝ :=
  ∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p.1 : ℝ) - 1) ^ 2)

/-- P0079 page 5 after (21): the singular series `𝔖(n) = 2 c0 𝔖'(n)`. -/
def singS (n : ℕ) : ℝ := 2 * twinC0 * Sprime n

/-- P0079 page 5: `S(1, L) = ∑_{m ≠ 0} r_{1,1}(m) 𝔖(m)`, written as the sum over the
representing pairs `m = 2^u - 2^v`, `1 ≤ u, v ≤ L`, `u ≠ v`; `𝔖` of a negative `m` is read
through `|m|`, as `𝔖'` depends only on the odd prime factors. -/
def S1 (N : ℕ) : ℝ :=
  ∑ u ∈ Icc 1 N, ∑ v ∈ (Icc 1 N).erase u, singS ((2 : ℤ) ^ u - 2 ^ v).natAbs

/-! ### The three cited inputs -/

/-- CITED, sorry. P0079 page 6, Lemma 3 (Bombieri and Davenport [1], Theorem 2), with
Chen's constant `B = 3.9171` [3] as stated on page 6: `Z(X; 2n) < B 𝔖(n) X` for
`1 ≤ n ≤ (1 - ε) X / 2`, `X` large. The uniformity in `n` is the form used in (27),
where `n` runs up to a power of two of size about `X`. -/
theorem chen_lemma3_p2 (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    ∀ᶠ X : ℝ in atTop, ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ (1 - ε) * X / 2 →
      twinZ ε X n ≤ 3.9171 * singS n * X := by
  sorry

/-- CITED, sorry. P0079 page 5, Lemma 1 (Khalfalah and Pintz [10], Theorem 2) for `k = 1`,
together with the numerical bound (22), `A(1) < 0.2792521041`. The limit is taken along
integers `L`, which the real limit of the paper implies. -/
theorem khalfalah_pintz_lemma1_p2 :
    ∃ A : ℝ, Tendsto (fun N : ℕ => S1 N / (2 * (N : ℝ) ^ 2) - 1) atTop (nhds A) ∧
      A < 0.2792521041 := by
  sorry

/-- The prime number theorem in the form `θ(x) ~ x`, used on page 7 for display (26).
PROVED in `Burst8PNT.lean` from the lab's sorry-free port `MediumPNT`. -/
theorem theta_pnt_p2 : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (nhds 1) :=
  theta_div_tendsto_one_p2

/-! ### Display (23): the Fourier identity, PROVED -/

/-- P0079 page 6, display (23), pointwise expansion of `|S(λα) G(μα)|^2`. -/
theorem paired_square_expansion_p2 (l m L ε X α : ℝ) :
    (((‖primeSum293 ε X (l * α) * powerSum293 L (m * α)‖ ^ 2 : ℝ)) : ℂ) =
      ∑ m1 ∈ Icc 1 ⌊L⌋₊, ∑ m2 ∈ Icc 1 ⌊L⌋₊, ∑ p1 ∈ boxP ε X, ∑ p2 ∈ boxP ε X,
        ((log p1 * log p2 : ℝ) : ℂ) *
          character293 ((l * ((p1 : ℝ) - p2) + m * ((2 : ℝ) ^ m1 - 2 ^ m2)) * α) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  unfold primeSum293 powerSum293
  simp only [map_mul, map_sum, Complex.conj_ofReal]
  have e1 : ∀ x y z w : ℂ, x * z * (y * w) = (z * w) * (x * y) := fun _ _ _ _ => by ring
  rw [e1, sum_mul_sum, sum_mul_sum]
  simp_rw [sum_mul, mul_sum]
  apply sum_congr rfl; intro m1 _
  apply sum_congr rfl; intro m2 _
  apply sum_congr rfl; intro p1 _
  apply sum_congr rfl; intro p2 _
  rw [← character_neg353, ← character_neg353]
  have h : (l * ((p1 : ℝ) - p2) + m * ((2 : ℝ) ^ m1 - 2 ^ m2)) * α =
      (p1 : ℝ) * (l * α) + -((p2 : ℝ) * (l * α)) +
        ((2 : ℝ) ^ m1 * (m * α) + -((2 : ℝ) ^ m2 * (m * α))) := by ring
  rw [h, character_add293, character_add293, character_add293]
  push_cast
  ring

/-- P0079 page 6, display (23): `I = ∑ log p1 log p2 max(0, η - |λ(p1 - p2) + μ(2^m1 - 2^m2)|)`.
PROVED. -/
theorem paired_tent_identity_p2 (l m L η ε X : ℝ) (hη : 0 < η) :
    (∫ α : ℝ, pairedMoment396 l m L η ε X α) =
      ∑ m1 ∈ Icc 1 ⌊L⌋₊, ∑ m2 ∈ Icc 1 ⌊L⌋₊, ∑ p1 ∈ boxP ε X, ∑ p2 ∈ boxP ε X,
        log p1 * log p2 *
          max 0 (η - |l * ((p1 : ℝ) - p2) + m * ((2 : ℝ) ^ m1 - 2 ^ m2)|) := by
  let T := Icc 1 ⌊L⌋₊ ×ˢ (Icc 1 ⌊L⌋₊ ×ˢ (boxP ε X ×ˢ boxP ε X))
  let w : ℕ × ℕ × ℕ × ℕ → ℂ := fun x => ((log x.2.2.1 * log x.2.2.2 : ℝ) : ℂ)
  let φ : ℕ × ℕ × ℕ × ℕ → ℝ := fun x =>
    l * ((x.2.2.1 : ℝ) - x.2.2.2) + m * ((2 : ℝ) ^ x.1 - 2 ^ x.2.1)
  have key : ∀ α : ℝ, ((pairedMoment396 l m L η ε X α : ℝ) : ℂ) =
      (∑ x ∈ T, w x * character293 (φ x * α)) * (kernel293 η α : ℂ) := by
    intro α
    unfold pairedMoment396
    rw [Complex.ofReal_mul, paired_square_expansion_p2]
    simp only [T, w, φ, sum_product]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [key]
  rw [finite_kernel_integral293 T w φ η hη]
  simp only [T, w, φ, sum_product]
  push_cast
  rfl

/-! ### Displays (24) and (25): the lattice reduction, PROVED -/

/-- P0079 pages 6 to 7, display (24): for `η < |λ/a|`, the tent is `η` on the solutions of
`δ = 0` and vanishes elsewhere. -/
theorem tent_lattice_p2 (l m η : ℝ) (r : ℚ) (hl : l ≠ 0) (hm : m ≠ 0)
    (hr : (r : ℝ) = l / m) (hη : 0 < η) (hη' : η < |l / r.num|) (u v : ℤ) :
    max 0 (η - |l * (u : ℝ) + m * v|) = if l * (u : ℝ) + m * v = 0 then η else 0 := by
  have hnum : r.num ≠ 0 := by
    intro h
    have : (r : ℝ) = 0 := by rw [Rat.cast_def, h]; simp
    rw [hr] at this
    exact div_ne_zero hl hm this
  have hq : (r.den : ℤ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hr' : l / m = (r.num : ℝ) / ((r.den : ℤ) : ℝ) := by
    rw [← hr, Rat.cast_def]; push_cast; rfl
  have H := rational_lattice_lt_iff293 l m η r.num r.den u v hl hm hnum hq hr' hη hη'
  split_ifs with h0
  · rw [h0]; simp [hη.le]
  · have : η ≤ |l * (u : ℝ) + m * v| := by
      by_contra hc; exact h0 (H.mp (lt_of_not_ge hc))
    simp [this]

/-- P0079 page 7: the real equation `δ = 0` is the integral equation
`a (p1 - p2) + q (2^m1 - 2^m2) = 0` with `λ/μ = a/q` in lowest terms. -/
theorem delta_zero_iff_p2 (l m : ℝ) (r : ℚ) (hl : l ≠ 0) (hm : m ≠ 0)
    (hr : (r : ℝ) = l / m) (u v : ℤ) :
    l * (u : ℝ) + m * v = 0 ↔ r.num * u + (r.den : ℤ) * v = 0 := by
  have hqR : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hnumR : (r.num : ℝ) ≠ 0 := by
    intro h
    have : (r : ℝ) = 0 := by rw [Rat.cast_def, h]; simp
    rw [hr] at this
    exact div_ne_zero hl hm this
  have hrr : l / m = (r.num : ℝ) / r.den := by rw [← hr, Rat.cast_def]
  have hm' : m = l * r.den / r.num := by
    field_simp at hrr ⊢
    linarith
  have heq : l * (u : ℝ) + m * v = (l / r.num) * ((r.num * u + (r.den : ℤ) * v : ℤ) : ℝ) := by
    rw [hm']; push_cast; field_simp
  rw [heq, mul_eq_zero, or_iff_right (div_ne_zero hl hnumR)]
  exact_mod_cast Iff.rfl

/-! ### Display (27): the off-diagonal reduction, PROVED -/

/-- Logarithms of naturals are nonnegative. -/
theorem log_nat_nonneg_p2 (n : ℕ) : 0 ≤ log (n : ℝ) := Real.log_natCast_nonneg n

/-- P0079 page 7, display (27), one sign: the pairs with `p1 - p2 = 2n` are counted by
`Z(X; 2n)` with `p = p2`, `p' = p1`. -/
theorem pair_le_twinZ_p2 (ε X : ℝ) (n : ℕ) :
    (∑ p1 ∈ boxP ε X, ∑ p2 ∈ boxP ε X,
      if (p1 : ℤ) - p2 = 2 * n then log p1 * log p2 else 0) ≤ twinZ ε X n := by
  unfold twinZ
  rw [sum_comm]
  apply sum_le_sum
  intro p _
  calc (∑ p1 ∈ boxP ε X, if (p1 : ℤ) - p = 2 * n then log (p1 : ℝ) * log p else 0)
      = ∑ p1 ∈ boxP ε X, if (p1 : ℤ) - p = 2 * n then log (p : ℝ) * log p1 else 0 := by
        apply sum_congr rfl; intro x _; split_ifs <;> ring
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro x hx
        simp only [mem_filter, mem_range] at hx ⊢
        exact ⟨hx.1, hx.2.1⟩
      · intro x _ _
        split_ifs
        · exact mul_nonneg (log_nat_nonneg_p2 _) (log_nat_nonneg_p2 _)
        · exact le_rfl

/-- The pair sum with a fixed difference `p1 - p2 = d`, both primes in `[εX, X]`. -/
def pairSumD (ε X : ℝ) (d : ℤ) : ℝ :=
  ∑ p1 ∈ boxP ε X, ∑ p2 ∈ boxP ε X, if (p1 : ℤ) - p2 = d then log p1 * log p2 else 0

/-- The pair sum is symmetric in the sign of the difference. -/
theorem pairSumD_neg_p2 (ε X : ℝ) (d : ℤ) : pairSumD ε X (-d) = pairSumD ε X d := by
  unfold pairSumD
  rw [sum_comm]
  apply sum_congr rfl; intro x _
  apply sum_congr rfl; intro y _
  by_cases h : (x : ℤ) - y = d
  · rw [if_pos (by omega), if_pos h, mul_comm]
  · rw [if_neg (by omega), if_neg h]

/-- `c0 ≥ 0`: a product of factors in `[0, 1]`. -/
theorem twinC0_nonneg_p2 : 0 ≤ twinC0 := by
  unfold twinC0
  apply tprod_nonneg
  intro p
  have h3 : (3 : ℝ) ≤ p.1 := by exact_mod_cast p.2.2
  have h1 : 1 / ((p.1 : ℝ) - 1) ^ 2 ≤ 1 := by
    rw [div_le_one (by nlinarith)]; nlinarith
  linarith

theorem singS_nonneg_p2 (n : ℕ) : 0 ≤ singS n :=
  mul_nonneg (mul_nonneg (by norm_num) twinC0_nonneg_p2) (Sprime_pos293 n).le

/-- If `εX > 2`, every prime in the box is odd, so odd differences do not occur. -/
theorem pairSumD_odd_p2 (ε X : ℝ) (hX : 2 < ε * X) (d : ℤ) (hd : ¬ 2 ∣ d) :
    pairSumD ε X d = 0 := by
  unfold pairSumD
  apply sum_eq_zero; intro p1 hp1
  apply sum_eq_zero; intro p2 hp2
  rw [if_neg]
  intro h
  simp only [mem_filter, mem_range] at hp1 hp2
  have o1 : Odd p1 := hp1.2.1.odd_of_ne_two (by
    intro h2; have := hp1.2.2; rw [h2] at this; push_cast at this; linarith)
  have o2 : Odd p2 := hp2.2.1.odd_of_ne_two (by
    intro h2; have := hp2.2.2; rw [h2] at this; push_cast at this; linarith)
  obtain ⟨a, ha⟩ := o1
  obtain ⟨b, hb⟩ := o2
  apply hd
  refine ⟨(a : ℤ) - b, ?_⟩
  rw [← h, ha, hb]; push_cast; ring

/-- Display (20): `Z(X; 2n) = 0` once `2n > (1 - ε) X`. -/
theorem twinZ_large_p2 (ε X : ℝ) (n : ℕ) (hX : 0 ≤ X) (hn : (1 - ε) * X / 2 < n) :
    twinZ ε X n = 0 := by
  unfold twinZ
  apply sum_eq_zero; intro p hp
  apply sum_eq_zero; intro p' hp'
  rw [if_neg]
  intro h
  simp only [mem_filter, mem_range] at hp hp'
  have h1 : (p' : ℝ) ≤ X := by
    have := Nat.floor_le hX
    have h2 : (p' : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast Nat.lt_succ_iff.mp hp'.1
    linarith
  have h3 : (p' : ℝ) - p = 2 * n := by exact_mod_cast h
  linarith [hp.2.2]

/-- P0079 page 7, display (27) for one difference: with Lemma 3 at this `X`,
`∑_{p1 - p2 = d} log p1 log p2 ≤ B 𝔖(|d|) X` for `d ≠ 0`. PROVED from the hypothesis. -/
theorem pairSumD_le_p2 (ε X : ℝ) (hX0 : 0 ≤ X) (hX : 2 < ε * X)
    (H3 : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ (1 - ε) * X / 2 →
      twinZ ε X n ≤ 3.9171 * singS n * X)
    (d : ℤ) (hd : d ≠ 0) :
    pairSumD ε X d ≤ 3.9171 * singS d.natAbs * X := by
  have hB : 0 ≤ 3.9171 * singS d.natAbs * X :=
    mul_nonneg (mul_nonneg (by norm_num) (singS_nonneg_p2 _)) hX0
  by_cases hodd : 2 ∣ d
  swap
  · rw [pairSumD_odd_p2 ε X hX d hodd]; exact hB
  -- reduce to `d > 0`
  have key : ∀ e : ℤ, 0 < e → 2 ∣ e → pairSumD ε X e ≤ 3.9171 * singS e.natAbs * X := by
    intro e he he2
    obtain ⟨k, hk⟩ := he2
    have hk0 : 0 < k := by omega
    set n := k.toNat with hn
    have hkn : k = (n : ℤ) := by omega
    have hn1 : 1 ≤ n := by omega
    have hE : e.natAbs = 2 * n := by omega
    have hS : singS e.natAbs = singS n := by
      rw [hE]; unfold singS; rw [Sprime_two_mul293]
    rw [hS]
    have hP : pairSumD ε X e ≤ twinZ ε X n := by
      have := pair_le_twinZ_p2 ε X n
      unfold pairSumD
      convert this using 4 with p1 _ p2 _
      rw [hk, hkn]
    refine hP.trans ?_
    by_cases hsmall : (n : ℝ) ≤ (1 - ε) * X / 2
    · exact H3 n hn1 hsmall
    · rw [twinZ_large_p2 ε X n hX0 (lt_of_not_ge hsmall)]
      exact mul_nonneg (mul_nonneg (by norm_num) (singS_nonneg_p2 _)) hX0
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · rw [← pairSumD_neg_p2, show d.natAbs = (-d).natAbs by simp]
    exact key (-d) (by omega) (by obtain ⟨k, hk⟩ := hodd; exact ⟨-k, by omega⟩)
  · exact key d hpos hodd

/-- The sum over prime pairs with `δ = 0` for fixed `m1, m2`. -/
def solV (l m ε X : ℝ) (m1 m2 : ℕ) : ℝ :=
  ∑ p1 ∈ boxP ε X, ∑ p2 ∈ boxP ε X,
    if l * ((p1 : ℝ) - p2) + m * ((2 : ℝ) ^ m1 - 2 ^ m2) = 0 then log p1 * log p2 else 0

/-- P0079 page 7, display (26): the diagonal `m1 = m2` forces `p1 = p2`. -/
theorem solV_diag_p2 (l m ε X : ℝ) (hl : l ≠ 0) (m1 : ℕ) :
    solV l m ε X m1 m1 = ∑ p ∈ boxP ε X, log p * log p := by
  unfold solV
  apply sum_congr rfl; intro p1 hp1
  have : ∀ p2 : ℕ, (l * ((p1 : ℝ) - p2) + m * ((2 : ℝ) ^ m1 - 2 ^ m1) = 0) ↔ p1 = p2 := by
    intro p2
    simp only [sub_self, mul_zero, add_zero, mul_eq_zero, hl, false_or, sub_eq_zero]
    exact_mod_cast Iff.rfl
  simp_rw [this]
  rw [sum_ite_eq]
  simp [hp1]

/-- P0079 page 7, displays (27) and the multiplicativity step before (28): for `m1 ≠ m2`,
the solutions contribute at most `B 𝔖'(q) 𝔖(2^m1 - 2^m2) X`. PROVED from Lemma 3 at `X`. -/
theorem solV_off_p2 (l m ε X : ℝ) (r : ℚ) (hl : l ≠ 0) (hm : m ≠ 0)
    (hr : (r : ℝ) = l / m) (hX0 : 0 ≤ X) (hX : 2 < ε * X)
    (H3 : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ (1 - ε) * X / 2 →
      twinZ ε X n ≤ 3.9171 * singS n * X)
    (m1 m2 : ℕ) (hne : m1 ≠ m2) :
    solV l m ε X m1 m2 ≤
      3.9171 * Sprime r.den * singS ((2 : ℤ) ^ m1 - 2 ^ m2).natAbs * X := by
  set a := r.num
  set q : ℤ := (r.den : ℤ)
  set D : ℤ := (2 : ℤ) ^ m1 - 2 ^ m2 with hD
  have hD0 : D ≠ 0 := by
    rw [hD, sub_ne_zero]
    intro h
    exact hne (Nat.pow_right_injective (le_refl 2) (by exact_mod_cast h))
  have hq0 : q ≠ 0 := by simp [q, r.den_ne_zero]
  have ha0 : a ≠ 0 := by
    intro h
    have : (r : ℝ) = 0 := by rw [Rat.cast_def]; simp [a] at h; simp [h]
    rw [hr] at this
    exact div_ne_zero hl hm this
  have hB0 : 0 ≤ 3.9171 * Sprime r.den * singS D.natAbs * X :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Sprime_pos293 _).le)
      (singS_nonneg_p2 _)) hX0
  have hcond : ∀ p1 p2 : ℕ, (l * ((p1 : ℝ) - p2) + m * ((2 : ℝ) ^ m1 - 2 ^ m2) = 0) ↔
      a * ((p1 : ℤ) - p2) = -(q * D) := by
    intro p1 p2
    have := delta_zero_iff_p2 l m r hl hm hr ((p1 : ℤ) - p2) D
    push_cast at this
    rw [hD] at this ⊢
    push_cast at this ⊢
    rw [this]
    constructor <;> intro h <;> linarith
  by_cases hdiv : a ∣ -(q * D)
  · obtain ⟨d, hd⟩ := hdiv
    have hd0 : d ≠ 0 := by
      rintro rfl
      simp at hd
      rcases hd with h | h
      · exact hq0 h
      · exact hD0 h
    have hV : solV l m ε X m1 m2 = pairSumD ε X d := by
      unfold solV pairSumD
      apply sum_congr rfl; intro p1 _
      apply sum_congr rfl; intro p2 _
      have : (l * ((p1 : ℝ) - p2) + m * ((2 : ℝ) ^ m1 - 2 ^ m2) = 0) ↔ (p1 : ℤ) - p2 = d := by
        rw [hcond, hd]
        exact ⟨fun h => mul_left_cancel₀ ha0 h, fun h => by rw [h]⟩
      simp only [this]
    rw [hV]
    refine (pairSumD_le_p2 ε X hX0 hX H3 d hd0).trans ?_
    -- `𝔖'(|d|) ≤ 𝔖'(q) 𝔖'(|D|)`
    have hdvd : d.natAbs ∣ r.den * D.natAbs := by
      have : d.natAbs * a.natAbs = r.den * D.natAbs := by
        have h2 := congrArg Int.natAbs hd
        simp only [Int.natAbs_neg, Int.natAbs_mul, q, Int.natAbs_natCast] at h2
        rw [h2]; ring
      exact Dvd.intro _ this
    have hne0 : r.den * D.natAbs ≠ 0 :=
      mul_ne_zero r.den_ne_zero (Int.natAbs_ne_zero.mpr hD0)
    have hS : Sprime d.natAbs ≤ Sprime r.den * Sprime D.natAbs :=
      (Sprime_dvd_le293 _ _ hdvd hne0).trans
        (Sprime_mul_le293 _ _ r.den_ne_zero (Int.natAbs_ne_zero.mpr hD0))
    unfold singS
    have hc := twinC0_nonneg_p2
    have hp := (Sprime_pos293 r.den).le
    have hx : 0 ≤ 3.9171 * 2 * twinC0 * X := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hS hx]
  · have hV : solV l m ε X m1 m2 = 0 := by
      unfold solV
      apply sum_eq_zero; intro p1 _
      apply sum_eq_zero; intro p2 _
      rw [if_neg]
      rw [hcond]
      intro h
      exact hdiv ⟨_, h.symm⟩
    rw [hV]; exact hB0

/-! ### Display (25): the moment is `η` times the solution sum, PROVED -/

/-- P0079 page 7, display (25): `I = η ∑_{δ = 0} log p1 log p2`. PROVED. -/
theorem moment_eq_solutions_p2 (l m L η ε X : ℝ) (r : ℚ) (hl : l ≠ 0) (hm : m ≠ 0)
    (hr : (r : ℝ) = l / m) (hη : 0 < η) (hη' : η < |l / r.num|) :
    (∫ α : ℝ, pairedMoment396 l m L η ε X α) =
      η * ∑ m1 ∈ Icc 1 ⌊L⌋₊, ∑ m2 ∈ Icc 1 ⌊L⌋₊, solV l m ε X m1 m2 := by
  rw [paired_tent_identity_p2 l m L η ε X hη]
  have ht : ∀ p1 p2 m1 m2 : ℕ,
      max 0 (η - |l * ((p1 : ℝ) - p2) + m * ((2 : ℝ) ^ m1 - 2 ^ m2)|) =
        if l * ((p1 : ℝ) - p2) + m * ((2 : ℝ) ^ m1 - 2 ^ m2) = 0 then η else 0 := by
    intro p1 p2 m1 m2
    have := tent_lattice_p2 l m η r hl hm hr hη hη' ((p1 : ℤ) - p2) ((2 : ℤ) ^ m1 - 2 ^ m2)
    push_cast at this
    exact this
  simp_rw [ht]
  unfold solV
  simp_rw [mul_sum]
  apply sum_congr rfl; intro m1 _
  apply sum_congr rfl; intro m2 _
  apply sum_congr rfl; intro p1 _
  apply sum_congr rfl; intro p2 _
  split_ifs <;> ring

/-- P0079 page 7, displays (26) to (28) before the limits: the solution sum is at most the
diagonal `⌊L⌋ ∑ log² p` plus `B 𝔖'(q) X S(1, ⌊L⌋)`. PROVED from Lemma 3 at `X`. -/
theorem solutions_le_p2 (l m ε X : ℝ) (r : ℚ) (hl : l ≠ 0) (hm : m ≠ 0)
    (hr : (r : ℝ) = l / m) (hX0 : 0 ≤ X) (hX : 2 < ε * X)
    (H3 : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ (1 - ε) * X / 2 →
      twinZ ε X n ≤ 3.9171 * singS n * X) (N : ℕ) :
    (∑ m1 ∈ Icc 1 N, ∑ m2 ∈ Icc 1 N, solV l m ε X m1 m2) ≤
      N * (∑ p ∈ boxP ε X, log p * log p) + 3.9171 * Sprime r.den * X * S1 N := by
  have hsplit : ∀ m1 ∈ Icc 1 N, (∑ m2 ∈ Icc 1 N, solV l m ε X m1 m2) =
      solV l m ε X m1 m1 + ∑ m2 ∈ (Icc 1 N).erase m1, solV l m ε X m1 m2 :=
    fun m1 hm1 => (add_sum_erase _ _ hm1).symm
  rw [sum_congr rfl hsplit, sum_add_distrib]
  simp_rw [solV_diag_p2 l m ε X hl]
  rw [sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
  gcongr
  unfold S1
  rw [mul_sum]
  apply sum_le_sum; intro m1 _
  rw [mul_sum]
  apply sum_le_sum; intro m2 hm2
  have hne : m2 ≠ m1 := (mem_erase.mp hm2).1
  refine (solV_off_p2 l m ε X r hl hm hr hX0 hX H3 m1 m2 (Ne.symm hne)).trans (le_of_eq ?_)
  ring

/-! ### Display (26): the diagonal with the prime number theorem -/

/-- P0079 page 7, display (26): `∑_{εX ≤ p ≤ X} log² p ≤ log X (θ(X) - θ(εX/2))`. PROVED. -/
theorem diag_theta_p2 (ε X : ℝ) (hε : 0 < ε) (hε' : ε < 1) (hX : 1 ≤ X) :
    (∑ p ∈ boxP ε X, log p * log p) ≤
      log X * (Chebyshev.theta X - Chebyshev.theta (ε * X / 2)) := by
  have hX0 : 0 ≤ X := by linarith
  have h1 : (∑ p ∈ boxP ε X, log (p : ℝ) * log p) ≤ ∑ p ∈ boxP ε X, log X * log p := by
    apply sum_le_sum; intro p hp
    simp only [mem_filter, mem_range] at hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.1.pos
    have hpX : (p : ℝ) ≤ X := by
      have := Nat.floor_le hX0
      have h2 : (p : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast Nat.lt_succ_iff.mp hp.1
      linarith
    exact mul_le_mul_of_nonneg_right (log_le_log hp0 hpX) (log_nat_nonneg_p2 p)
  rw [← mul_sum] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (log_nonneg hX))
  let Q := (Ioc 0 ⌊ε * X / 2⌋₊).filter (fun p : ℕ => p.Prime)
  let R := (Ioc 0 ⌊X⌋₊).filter (fun p : ℕ => p.Prime)
  have hdisj : Disjoint (boxP ε X) Q := by
    rw [disjoint_left]
    intro p hp hq
    simp only [Q, mem_filter, mem_Ioc, mem_range] at hp hq
    have h2 : (p : ℝ) ≤ ⌊ε * X / 2⌋₊ := by exact_mod_cast hq.1.2
    have h3 := Nat.floor_le (show 0 ≤ ε * X / 2 by positivity)
    have h4 : 0 < ε * X := by nlinarith
    linarith [hp.2.2]
  have hsub : boxP ε X ∪ Q ⊆ R := by
    intro p hp
    simp only [Q, R, mem_union, mem_filter, mem_Ioc, mem_range] at hp ⊢
    rcases hp with hp | hp
    · exact ⟨⟨hp.2.1.pos, Nat.lt_succ_iff.mp hp.1⟩, hp.2.1⟩
    · refine ⟨⟨hp.1.1, hp.1.2.trans (Nat.floor_le_floor ?_)⟩, hp.2⟩
      nlinarith
  have hθX : Chebyshev.theta X = ∑ p ∈ R, log (p : ℝ) := rfl
  have hθY : Chebyshev.theta (ε * X / 2) = ∑ p ∈ Q, log (p : ℝ) := rfl
  have := sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => log_nat_nonneg_p2 p)
  rw [sum_union hdisj] at this
  rw [hθX, hθY]
  linarith

/-- From `θ(x) ~ x`: for every `δ > 0`, eventually `(1 - δ) x ≤ θ(x) ≤ (1 + δ) x`. -/
theorem theta_bounds_p2 (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, (1 - δ) * x ≤ Chebyshev.theta x ∧ Chebyshev.theta x ≤ (1 + δ) * x := by
  have h := (theta_pnt_p2.eventually (Metric.ball_mem_nhds 1 hδ))
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  rw [Real.dist_eq, abs_lt] at hx
  obtain ⟨h1, h2⟩ := hx
  constructor
  · have := (le_div_iff₀ hx0).mp (by linarith : 1 - δ ≤ Chebyshev.theta x / x)
    linarith
  · have := (div_le_iff₀ hx0).mp (by linarith : Chebyshev.theta x / x ≤ 1 + δ)
    linarith

/-! ### Display (28): the limit of Lemma 1 -/

/-- P0079 page 7, display (28): from Lemma 1 and (22), eventually
`S(1, N) ≤ 2 (1 + 0.2792521041) N²`. PROVED from the cited Lemma 1. -/
theorem S1_eventually_p2 :
    ∀ᶠ N : ℕ in atTop, S1 N ≤ 2 * (1 + 0.2792521041) * (N : ℝ) ^ 2 := by
  obtain ⟨A, hA, hA'⟩ := khalfalah_pintz_lemma1_p2
  have h := hA.eventually (eventually_lt_nhds hA')
  filter_upwards [h, eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < 2 * (N : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    positivity
  have := (div_lt_iff₀ hN0).mp (by linarith : S1 N / (2 * (N : ℝ) ^ 2) < 1 + 0.2792521041)
  linarith

/-! ### Lemma 4 with the constant of display (28) -/

/-- P0079 pages 6 to 7, Lemma 4 with the constant `2 B (1 + A(1))` of display (28), the exact
statement of the session 4 leaf `Burst4Split.paired_second_moment_sharpB4`.
CONDITIONAL ON `chen_lemma3_p2` and `khalfalah_pintz_lemma1_p2`; `theta_pnt_p2` is
PROVED. This proof has no sorry of its own. -/
theorem paired_second_moment_p2 (s : ℕ) (μ : ℕ → ℝ) (l m η ε : ℝ)
    (hM : 0 < ∑ i : Fin s, |μ i|) (hl : l ≠ 0) (hm : m ≠ 0)
    (r : ℚ) (hr : (r : ℝ) = l / m) (hη : 0 < η) (hη' : η < |l / r.num|)
    (hε : 0 < ε) (hε' : ε < 1) :
    ∀ᶠ X : ℝ in atTop,
      (∫ α : ℝ, pairedMoment396 l m (cutoff293 s μ ε X) η ε X α) ≤
        (log 2 + bigCSharpB4 * Sprime r.den) * η * X * (cutoff293 s μ ε X) ^ 2 := by
  set M := ∑ i : Fin s, |μ i|
  set c := log (2 * M) - log ε
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  set K := max 0 (c * (1 - ε / 4) / (ε / 4 * log 2))
  have hcut := cutoff_tendsto353 s μ ε hM hε
  have hfloor : Tendsto (fun X => ⌊cutoff293 s μ ε X⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp hcut
  have hhalf : Tendsto (fun X : ℝ => ε * X / 2) atTop atTop := by
    have : Tendsto (fun X : ℝ => (ε / 2) * X) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity) tendsto_id
    convert this using 2; ring
  filter_upwards [chen_lemma3_p2 ε hε hε', eventually_ge_atTop (1 : ℝ),
    eventually_gt_atTop (2 / ε),
    theta_bounds_p2 (ε / 8) (by positivity),
    hhalf.eventually (theta_bounds_p2 (ε / 8) (by positivity)),
    hfloor.eventually S1_eventually_p2,
    hcut.eventually (eventually_ge_atTop K)] with X H3 hX1 hXe hθ hθh hS1 hLK
  set L := cutoff293 s μ ε X with hL
  set N := ⌊L⌋₊
  have hX0 : 0 ≤ X := by linarith
  have hXε : 2 < ε * X := by
    have := (div_lt_iff₀ hε).mp hXe; linarith
  have hL0 : 0 ≤ L := le_trans (le_max_left _ _) hLK
  have hNL : (N : ℝ) ≤ L := Nat.floor_le hL0
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  -- `log X = L log 2 + c`
  have hlogX : log X = L * log 2 + c := by
    have hpos : 0 < ε * X / (2 * M) := by positivity
    have h := Real.log_div_log (b := 2) (x := ε * X / (2 * M))
    rw [hL]
    unfold cutoff293
    rw [← h, div_mul_cancel₀ _ hlog2.ne', Real.log_div (by positivity) (by positivity),
      Real.log_mul hε.ne' (by positivity)]
    ring
  have hlogX0 : 0 ≤ log X := log_nonneg hX1
  -- the diagonal
  have hD : (∑ p ∈ boxP ε X, log p * log p) ≤ log X * (X * (1 - ε / 4)) := by
    refine (diag_theta_p2 ε X hε hε' hX1).trans (mul_le_mul_of_nonneg_left ?_ hlogX0)
    have h1 := hθ.2
    have h2 := hθh.1
    nlinarith
  have hLc : c * (1 - ε / 4) ≤ ε / 4 * log 2 * L := by
    have h := le_trans (le_max_right _ _) hLK
    rw [div_le_iff₀ (by positivity)] at h
    linarith
  have hdiag : (N : ℝ) * (∑ p ∈ boxP ε X, log p * log p) ≤ log 2 * X * L ^ 2 := by
    calc (N : ℝ) * (∑ p ∈ boxP ε X, log p * log p)
        ≤ L * (log X * (X * (1 - ε / 4))) := by
          apply mul_le_mul hNL hD (sum_nonneg (fun p _ =>
            mul_nonneg (log_nat_nonneg_p2 p) (log_nat_nonneg_p2 p))) hL0
      _ = X * (L * ((L * log 2 + c) * (1 - ε / 4))) := by rw [hlogX]; ring
      _ ≤ X * (L * (L * log 2)) := by
          apply mul_le_mul_of_nonneg_left _ hX0
          apply mul_le_mul_of_nonneg_left _ hL0
          nlinarith
      _ = log 2 * X * L ^ 2 := by ring
  -- the off-diagonal
  have hS1' : S1 N ≤ 2 * (1 + 0.2792521041) * L ^ 2 := by
    refine hS1.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    exact pow_le_pow_left₀ hN0 hNL 2
  have hoff : 3.9171 * Sprime r.den * X * S1 N ≤ bigCSharpB4 * Sprime r.den * X * L ^ 2 := by
    have hq := (Sprime_pos293 r.den).le
    have : 0 ≤ 3.9171 * Sprime r.den * X := by positivity
    calc 3.9171 * Sprime r.den * X * S1 N
        ≤ 3.9171 * Sprime r.den * X * (2 * (1 + 0.2792521041) * L ^ 2) :=
          mul_le_mul_of_nonneg_left hS1' this
      _ = bigCSharpB4 * Sprime r.den * X * L ^ 2 := by unfold bigCSharpB4; ring
  rw [moment_eq_solutions_p2 l m L η ε X r hl hm hr hη hη']
  have hW := solutions_le_p2 l m ε X r hl hm hr hX0 hXε H3 N
  calc η * ∑ m1 ∈ Icc 1 N, ∑ m2 ∈ Icc 1 N, solV l m ε X m1 m2
      ≤ η * (log 2 * X * L ^ 2 + bigCSharpB4 * Sprime r.den * X * L ^ 2) :=
        mul_le_mul_of_nonneg_left (hW.trans (by linarith)) hη.le
    _ = (log 2 + bigCSharpB4 * Sprime r.den) * η * X * L ^ 2 := by ring

/-- The type agrees with the session 4 leaf. -/
example : ∀ (s : ℕ) (μ : ℕ → ℝ) (l m η ε : ℝ)
    (_ : 0 < ∑ i : Fin s, |μ i|) (_ : l ≠ 0) (_ : m ≠ 0)
    (r : ℚ) (_ : (r : ℝ) = l / m) (_ : 0 < η) (_ : η < |l / r.num|)
    (_ : 0 < ε) (_ : ε < 1),
    ∀ᶠ X : ℝ in atTop,
      (∫ α : ℝ, pairedMoment396 l m (cutoff293 s μ ε X) η ε X α) ≤
        (log 2 + bigCSharpB4 * Sprime r.den) * η * X * (cutoff293 s μ ε X) ^ 2 :=
  paired_second_moment_p2

end LeanLab.LZPowersOfTwo.Burst8P2
