import LeanLab.ExceptionalSet.MVMajorArcs
import LeanLab.ExceptionalSet.MVMajorSing
import LeanLab.ExceptionalSet.MVVinogradovProved

/-!
# Estermann's major arc part, explicit form

Lab proof, unit U-6250, CLOUD 20261020T0917Z-cloud39. AI wrote the Lean code. Known
mathematics, Vaughan's book Chapter 3. Binary Goldbach is OPEN.

For `M = 2x + 1`, `Q ≥ 1` with `2Q³ < M`, `n < M` and the major arc approximation
`‖S(a/q + β) - μ(q)/φ(q) V(β)‖ ≤ E (1 + 2π|β|x)` for every `q ≤ Q`:

* `arcMV_sum`: one arc around `a/q` contributes `(μ(q)/φ(q))² e(an/q) M J2(n)` up to
  `(2Q + 1) D (x log x + x) + φ(q)^{-2} (2M/δ + 1/(2δ²))`, `δ = Q/M`,
  `D = ψ(x) - θ(x) + E (1 + 2πxQ/M)`.
* `majorPart_explicit`: the major arc part of `MVEstermann.lean` at `n` is
  `M J2(n) ∑_{q ≤ Q} μ(q)² c_q(n)/φ(q)²` up to
  `Q² (2Q + 1) D (x log x + x) + (∑_{q ≤ Q} 1/φ(q)) (2M/δ + 1/(2δ²))`.
-/

namespace LeanLab.ExceptionalSet.MVMajor

open Complex Finset Real ZMod
open scoped ArithmeticFunction.Moebius
open LeanLab.PNTPort.Vinogradov LeanLab.PNTPort.LargeSieve LeanLab.ExceptionalSet.MV

attribute [local instance] Classical.propDecidable

lemma norm_dft_logPrimes_le (x : ℕ) (k : ZMod (Mx x)) :
    ‖𝓕 (logPrimes x) k‖ ≤ x * Real.log x := by
  rw [dft_logPrimes_eq]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ n ∈ (Icc 1 x).filter Nat.Prime,
        ‖(Real.log n : ℂ) * e ((n : ℝ) * (-(ZMod.val k : ℝ) / (Mx x : ℝ)))‖
      ≤ ∑ n ∈ Icc 1 x, Real.log x := by
        refine (sum_le_sum fun n hn => ?_).trans
          (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ =>
            Real.log_natCast_nonneg x)
        rw [mem_filter, mem_Icc] at hn
        rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_of_nonneg
          (Real.log_natCast_nonneg n)]
        exact Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) (by exact_mod_cast hn.1.2)
    _ = x * Real.log x := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp

/-- The approximation on one Estermann arc. -/
theorem arcMV_approx {x : ℕ} {Q : ℝ} {q a : ℕ} (hq : 1 ≤ q) (hcop : Nat.Coprime a q) {E : ℝ}
    (hmaj : ∀ a' : ℤ, IsCoprime a' (q : ℤ) → ∀ β : ℝ,
      ‖S x (a' / q + β) - (μ q : ℂ) / q.totient * V x β‖ ≤ E * (1 + 2 * π * |β| * x))
    {k : ZMod (Mx x)} (hk : k ∈ arcMV x Q q a) :
    ‖𝓕 (logPrimes x) k - (μ q : ℂ) / q.totient *
        V x (-((k.val : ℝ) / (Mx x) - (a : ℝ) / q))‖ ≤
      (Chebyshev.psi x - Chebyshev.theta x) + E * (1 + 2 * π * x * Q / (Mx x)) := by
  have hd : dist0 ((k.val : ℝ) / (Mx x) - (a : ℝ) / q) ≤ Q / (Mx x) := by
    simp only [arcMV, Finset.mem_filter] at hk; exact hk.2
  set θ := (k.val : ℝ) / (Mx x) - (a : ℝ) / q with hθ
  set j := round θ with hj
  set β := θ - j with hβ
  have hβd : |β| = dist0 θ := rfl
  have hc : IsCoprime (-((a : ℤ) + q * j)) (q : ℤ) := by
    have : IsCoprime (a : ℤ) (q : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast hcop
    exact (this.add_mul_left_left j).neg_left
  have h1 := hmaj _ hc (-β)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have e1 : ((-((a : ℤ) + q * j) : ℤ) : ℝ) / q + -β = -(k.val : ℝ) / (Mx x) := by
    rw [hβ, hθ]; push_cast; field_simp; ring
  have e2 : V x (-β) = V x (-θ) := by
    rw [hβ, show -(θ - (j : ℝ)) = -θ + ((j : ℤ) : ℝ) by ring, V_add_int]
  rw [e1, e2, abs_neg] at h1
  have h0 := norm_dft_sub_S_le x k
  have hE : 0 ≤ E := by
    have := le_trans (norm_nonneg _) h1
    have hpos : 0 < 1 + 2 * π * |β| * x := by positivity
    exact nonneg_of_mul_nonneg_left this hpos
  have h2 : E * (1 + 2 * π * |β| * x) ≤ E * (1 + 2 * π * x * Q / (Mx x)) := by
    apply mul_le_mul_of_nonneg_left _ hE
    rw [hβd]
    have hM : (0 : ℝ) < Mx x := by unfold Mx; positivity
    have h3 := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 2 * π * x by positivity)
    have : 2 * π * x * (Q / (Mx x)) = 2 * π * x * Q / (Mx x) := by ring
    nlinarith
  calc ‖𝓕 (logPrimes x) k - (μ q : ℂ) / q.totient * V x (-θ)‖
      = ‖(𝓕 (logPrimes x) k - S x (-(k.val : ℝ) / (Mx x))) +
          (S x (-(k.val : ℝ) / (Mx x)) - (μ q : ℂ) / q.totient * V x (-θ))‖ := by
        congr 1; ring
    _ ≤ ‖𝓕 (logPrimes x) k - S x (-(k.val : ℝ) / (Mx x))‖ +
          ‖S x (-(k.val : ℝ) / (Mx x)) - (μ q : ℂ) / q.totient * V x (-θ)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add h0 (h1.trans h2)

/-- One Estermann arc: its contribution against the main term. -/
theorem arcMV_sum {x : ℕ} {Q : ℝ} (hQ : 0 < Q) {q a n : ℕ} (hq : 1 ≤ q)
    (hcop : Nat.Coprime a q) (hn : n < Mx x) {E : ℝ}
    (hmaj : ∀ a' : ℤ, IsCoprime a' (q : ℤ) → ∀ β : ℝ,
      ‖S x (a' / q + β) - (μ q : ℂ) / q.totient * V x β‖ ≤ E * (1 + 2 * π * |β| * x)) :
    ‖∑ k ∈ arcMV x Q q a, 𝓕 (logPrimes x) k ^ 2 * (stdAddChar ((n : ZMod (Mx x)) * k) : ℂ) -
        ((μ q : ℂ) / q.totient) ^ 2 * e (n * ((a : ℝ) / q)) * ((Mx x : ℂ) * (J2 x n : ℂ))‖ ≤
      (2 * Q + 1) * (((Chebyshev.psi x - Chebyshev.theta x) +
          E * (1 + 2 * π * x * Q / (Mx x))) * (x * Real.log x + x)) +
        1 / (q.totient : ℝ) ^ 2 * (2 * (Mx x) / (Q / (Mx x)) + 1 / (2 * (Q / (Mx x)) ^ 2)) := by
  set M := Mx x with hMdef
  have hM : (0 : ℝ) < M := by rw [hMdef]; unfold Mx; positivity
  have h2x : 2 * x < M := by rw [hMdef]; unfold Mx; omega
  set D := (Chebyshev.psi x - Chebyshev.theta x) + E * (1 + 2 * π * x * Q / M) with hD
  set c : ℂ := (μ q : ℂ) / q.totient with hc
  set θ : ZMod M → ℝ := fun k => (k.val : ℝ) / M - (a : ℝ) / q with hθ
  have hc1 : ‖c‖ ≤ 1 / (q.totient : ℝ) := norm_mu_div_le q hq
  have ht1 : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hc0 : ‖c‖ ≤ 1 := hc1.trans (by rw [div_le_one (by linarith)]; exact ht1)
  -- the characters split
  have hchar : ∀ k : ZMod M, (stdAddChar ((n : ZMod M) * k) : ℂ) =
      e (n * ((a : ℝ) / q)) * e (n * θ k) := by
    intro k
    rw [stdAddChar_nat_mul, ← e_add]
    congr 1; simp only [hθ]; ring
  -- pointwise
  have hpt : ∀ k ∈ arcMV x Q q a,
      ‖(𝓕 (logPrimes x) k ^ 2 - (c * V x (-θ k)) ^ 2) * (stdAddChar ((n : ZMod M) * k) : ℂ)‖ ≤
        D * (x * Real.log x + x) := by
    intro k hk
    have h1 := arcMV_approx hq hcop hmaj hk
    have hF := norm_dft_logPrimes_le x k
    have hW : ‖c * V x (-θ k)‖ ≤ x := by
      rw [norm_mul]
      calc ‖c‖ * ‖V x (-θ k)‖ ≤ 1 * x :=
            mul_le_mul hc0 (norm_V_le x _) (norm_nonneg _) zero_le_one
        _ = x := one_mul _
    rw [norm_mul, show ‖(stdAddChar ((n : ZMod M) * k) : ℂ)‖ = 1 by
      rw [hchar, norm_mul, norm_e, norm_e, one_mul], mul_one]
    rw [sq_sub_sq, norm_mul, mul_comm]
    apply mul_le_mul h1 _ (norm_nonneg _) (le_trans (norm_nonneg _) h1)
    exact (norm_add_le _ _).trans (by linarith)
  have hcard : ((arcMV x Q q a).card : ℝ) ≤ 2 * Q + 1 := by
    have := card_arc_le (M := M) ((a : ℝ) / q) (div_nonneg hQ.le hM.le)
    have e1 : 2 * (Q / M) * M + 1 = 2 * Q + 1 := by field_simp
    rw [e1] at this
    exact this
  -- the complete sum and the tail
  have hfull := full_sum_V2 (N := x) (M := M) h2x hn ((a : ℝ) / q)
  have hsplit := sum_add_sum_compl (arcMV x Q q a)
    (fun k : ZMod M => V x (-θ k) ^ 2 * e (n * θ k))
  have htail : ‖∑ k ∈ (arcMV x Q q a)ᶜ, V x (-θ k) ^ 2 * e (n * θ k)‖ ≤
      2 * M / (Q / M) + 1 / (2 * (Q / M) ^ 2) := by
    refine (norm_sum_le _ _).trans ?_
    have hT : ∀ k ∈ (arcMV x Q q a)ᶜ, Q / M < dist0 ((k.val : ℝ) / M - (a : ℝ) / q) := by
      intro k hk
      rw [mem_compl, arcMV, mem_filter] at hk
      push_neg at hk
      exact hk (mem_univ _)
    refine le_trans (le_of_eq ?_) (tail_V2_le (N := x) ((a : ℝ) / q) (div_pos hQ hM) _ hT)
    refine sum_congr rfl fun k _ => ?_
    rw [norm_mul, norm_e, mul_one, norm_pow]
  -- assemble
  have hmain : ∑ k ∈ arcMV x Q q a, (c * V x (-θ k)) ^ 2 * (stdAddChar ((n : ZMod M) * k) : ℂ) =
      c ^ 2 * e (n * ((a : ℝ) / q)) *
        ((M : ℂ) * (J2 x n : ℂ) - ∑ k ∈ (arcMV x Q q a)ᶜ, V x (-θ k) ^ 2 * e (n * θ k)) := by
    have : (M : ℂ) * (J2 x n : ℂ) - ∑ k ∈ (arcMV x Q q a)ᶜ, V x (-θ k) ^ 2 * e (n * θ k) =
        ∑ k ∈ arcMV x Q q a, V x (-θ k) ^ 2 * e (n * θ k) := by
      rw [← hfull]
      simp only [hθ] at hsplit ⊢
      rw [← hsplit]; ring
    rw [this, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [hchar]; ring
  have hdecomp : ∑ k ∈ arcMV x Q q a, 𝓕 (logPrimes x) k ^ 2 *
        (stdAddChar ((n : ZMod M) * k) : ℂ) - c ^ 2 * e (n * ((a : ℝ) / q)) *
        ((M : ℂ) * (J2 x n : ℂ)) =
      ∑ k ∈ arcMV x Q q a, (𝓕 (logPrimes x) k ^ 2 - (c * V x (-θ k)) ^ 2) *
        (stdAddChar ((n : ZMod M) * k) : ℂ) -
        c ^ 2 * e (n * ((a : ℝ) / q)) *
          ∑ k ∈ (arcMV x Q q a)ᶜ, V x (-θ k) ^ 2 * e (n * θ k) := by
    have : ∑ k ∈ arcMV x Q q a, (𝓕 (logPrimes x) k ^ 2 - (c * V x (-θ k)) ^ 2) *
        (stdAddChar ((n : ZMod M) * k) : ℂ) =
        ∑ k ∈ arcMV x Q q a, 𝓕 (logPrimes x) k ^ 2 * (stdAddChar ((n : ZMod M) * k) : ℂ) -
        ∑ k ∈ arcMV x Q q a, (c * V x (-θ k)) ^ 2 * (stdAddChar ((n : ZMod M) * k) : ℂ) := by
      rw [← sum_sub_distrib]; refine sum_congr rfl fun k _ => ?_; ring
    rw [this, hmain]; ring
  rw [hdecomp]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans ?_
    refine (sum_le_sum hpt).trans ?_
    rw [sum_const, nsmul_eq_mul]
    have hD0 : 0 ≤ D * (x * Real.log x + x) := by
      have hpsi : 0 ≤ Chebyshev.psi (x : ℝ) - Chebyshev.theta x := by
        have := Chebyshev.theta_le_psi (x : ℝ); linarith
      have hE : 0 ≤ E := by
        have h := hmaj (a : ℤ) (by
          rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast hcop) 0
        have := le_trans (norm_nonneg _) h
        simpa using this
      have : 0 ≤ D := by rw [hD]; positivity
      have : 0 ≤ (x : ℝ) * Real.log x + x := by
        have := Real.log_natCast_nonneg x; positivity
      positivity
    exact mul_le_mul_of_nonneg_right hcard hD0
  · rw [norm_mul, norm_mul, norm_e, mul_one, norm_pow]
    apply mul_le_mul _ htail (norm_nonneg _) (by positivity)
    calc ‖c‖ ^ 2 ≤ (1 / (q.totient : ℝ)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hc1 2
      _ = 1 / (q.totient : ℝ) ^ 2 := by ring

/-- **The major arc part, explicit form.** -/
theorem majorPart_explicit {x : ℕ} {Q : ℝ} (hQ : 1 ≤ Q) (hQM : 2 * Q ^ 3 < Mx x) {n : ℕ}
    (hn : n < Mx x) {E : ℝ}
    (hmaj : ∀ q ∈ Icc 1 ⌊Q⌋₊, ∀ a' : ℤ, IsCoprime a' (q : ℤ) → ∀ β : ℝ,
      ‖S x (a' / q + β) - (μ q : ℂ) / q.totient * V x β‖ ≤ E * (1 + 2 * π * |β| * x)) :
    ‖majorPart (logPrimes x) (minorArcs x Q) (n : ZMod (Mx x)) -
        (Mx x : ℂ) * (J2 x n : ℂ) * ((∑ q ∈ Icc 1 ⌊Q⌋₊, f2 n q : ℝ) : ℂ)‖ ≤
      Q ^ 2 * ((2 * Q + 1) * (((Chebyshev.psi x - Chebyshev.theta x) +
          E * (1 + 2 * π * x * Q / (Mx x))) * (x * Real.log x + x))) +
        (∑ q ∈ Icc 1 ⌊Q⌋₊, 1 / (q.totient : ℝ)) *
          (2 * (Mx x) / (Q / (Mx x)) + 1 / (2 * (Q / (Mx x)) ^ 2)) := by
  set P := ⌊Q⌋₊ with hP
  set R := (2 * Q + 1) * (((Chebyshev.psi x - Chebyshev.theta x) +
          E * (1 + 2 * π * x * Q / (Mx x))) * (x * Real.log x + x)) with hR
  set T0 := 2 * (Mx x) / (Q / (Mx x)) + 1 / (2 * (Q / (Mx x)) ^ 2) with hT0
  have hQ0 : 0 < Q := by linarith
  unfold majorPart
  rw [minorArcs, compl_compl, majorArcs_eq, sum_biUnion (arcsMV_disjoint hQ hQM)]
  rw [← singP2_eq, singP2, mul_sum, ← sum_sub_distrib]
  have harc : ∀ p ∈ majIdx P,
      ‖∑ k ∈ arcMV x Q p.1 p.2, 𝓕 (logPrimes x) k ^ 2 * (stdAddChar ((n : ZMod (Mx x)) * k) : ℂ) -
        (Mx x : ℂ) * (J2 x n : ℂ) * (((μ p.1 : ℂ) / p.1.totient) ^ 2 *
          e (n * ((p.2 : ℝ) / p.1)))‖ ≤ R + 1 / (p.1.totient : ℝ) ^ 2 * T0 := by
    intro p hp
    have hp' := hp
    simp only [majIdx, mem_filter, mem_product, mem_Icc, mem_range] at hp'
    have h := arcMV_sum hQ0 (n := n) hp'.1.1.1 hp'.2.2 hn (hmaj p.1 (by
      rw [mem_Icc]; exact hp'.1.1))
    rw [show (Mx x : ℂ) * (J2 x n : ℂ) * (((μ p.1 : ℂ) / p.1.totient) ^ 2 *
        e (n * ((p.2 : ℝ) / p.1))) = ((μ p.1 : ℂ) / p.1.totient) ^ 2 *
        e (n * ((p.2 : ℝ) / p.1)) * ((Mx x : ℂ) * (J2 x n : ℂ)) by ring]
    exact h
  refine (norm_sum_le _ _).trans ((sum_le_sum harc).trans ?_)
  rw [sum_add_distrib, sum_const, nsmul_eq_mul]
  have hsum := sum_majIdx P (fun q => 1 / (q.totient : ℝ) ^ 2 * T0)
  rw [hsum]
  have hR0 : 0 ≤ R := by
    have hpsi : 0 ≤ Chebyshev.psi (x : ℝ) - Chebyshev.theta x := by
      have := Chebyshev.theta_le_psi (x : ℝ); linarith
    have hE : 0 ≤ E := by
      have h := hmaj 1 (by rw [mem_Icc]; exact ⟨le_rfl, Nat.le_floor (by simpa using hQ)⟩)
        0 (by rw [isCoprime_zero_left]; simp) 0
      have := le_trans (norm_nonneg _) h
      simpa using this
    have : 0 ≤ (x : ℝ) * Real.log x + x := by
      have := Real.log_natCast_nonneg x; positivity
    rw [hR]; positivity
  have hcardP : ((majIdx P).card : ℝ) ≤ Q ^ 2 :=
    (card_majIdx_le P).trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hQ0.le) 2)
  apply add_le_add (mul_le_mul_of_nonneg_right hcardP hR0)
  rw [sum_mul]
  refine le_of_eq (sum_congr rfl fun q hq => ?_)
  rw [mem_Icc] at hq
  have : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 (by omega)).ne'
  field_simp

end LeanLab.ExceptionalSet.MVMajor
