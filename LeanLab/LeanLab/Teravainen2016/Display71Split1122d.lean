/-
P0076 J. Teräväinen, arXiv 1611.08585: a split of the HARD LEAFs `display71_dyad` and
`display71_half` of Prop51Split1122b.lean, display (7.1) on page 30. The analytic content sits in
two cited LEAFs, Theorem 6.5 on page 22 on a general range and Hypothesis 6.4 for the phases
`e(ξ m)` of (7.3), proved in Section 10. The linearity step, Hypothesis 6.4 for `ω_m` from
Hypothesis 6.4 for each `e(ξ m)` by the expansion (2.2), is proved here.
burst-20261122 step display71_split1122d. AI wrote the Lean code. The binary Goldbach
conjecture is OPEN.
-/
import LeanLab.Teravainen2016.Prop51Split1122b

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-! ### Definitions for Hypothesis 6.4, page 22 -/

/-- The support sets of the sieve weights of Theorem 1.5, page 4: `d = p₁ ⋯ p_r` squarefree,
`d ≤ D`, `z ≥ p₁ > ⋯ > p_r`, and `p₁ ⋯ p_{m-1} p_m^{β+1} ≤ D` for every odd `m` in the upper
case and every even `m` in the lower case. The semilinear sets `D^{±,SEM}` have `β = 1`; the
linear weights of Hypothesis 6.4 have `β = 2`. Index `j` below is `m - 1`. -/
def SieveAdmissible (D z : ℝ) (lower : Bool) (β : ℕ) (d : ℕ) : Prop :=
  Squarefree d ∧ (d : ℝ) ≤ D ∧ (∀ p ∈ d.primeFactors, (p : ℝ) ≤ z) ∧
    ∀ j < d.primeFactorsList.length, j % 2 = (if lower then 1 else 0) →
      ((((d.primeFactorsList.reverse.take (j + 1)).prod *
          (d.primeFactorsList.reverse.getD j 0) ^ β : ℕ)) : ℝ) ≤ D

/-- The sieve weights `λ_d` of Theorem 1.5, page 4: the Möbius function restricted to the
support set `SieveAdmissible`. -/
noncomputable def sieveWeight (D z : ℝ) (lower : Bool) (β : ℕ) (d : ℕ) : ℝ :=
  if SieveAdmissible D z lower β d then (ArithmeticFunction.moebius d : ℝ) else 0

/-- Definition 6.2, page 21: `g` is of convolution type for the scale `X` and `σ`, that is
`g(ℓ) = ∑_{ℓ = k m, X^{1/σ} ≤ k ≤ X^{1-1/σ}} α_k β_m` with `|α_k|, |β_k| ≤ τ(k)² log k`. -/
def ConvType (X σ : ℝ) (g : ℕ → ℂ) : Prop :=
  ∃ a β : ℕ → ℂ, (∀ k, ‖a k‖ ≤ (k.divisors.card : ℝ) ^ 2 * Real.log k) ∧
    (∀ k, ‖β k‖ ≤ (k.divisors.card : ℝ) ^ 2 * Real.log k) ∧
    ∀ ℓ, g ℓ = ∑ k ∈ ℓ.divisors.filter
      (fun k : ℕ => X ^ (1 / σ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ X ^ (1 - 1 / σ)), a k * β (ℓ / k)

/-- The first sum of Hypothesis 6.4, page 22, for `L(n) = K n + c`, the weights `ω` on the
range `M` that plays `n ∼ N`, the scale `X` that plays `N`, `δ = (c - 1, K)`, the upper linear
sieve weights of level `X^{ρ₁}` and sifting parameter `X^{1/5}`, and `g` on `ℓ ≤ X^{0.9}`. -/
noncomputable def linDisc (ρ₁ X : ℝ) (K c : ℤ) (M : Finset ℕ) (ω : ℕ → ℂ) (g : ℕ → ℂ) : ℂ :=
  ∑ d ∈ (range (⌊X ^ ρ₁⌋₊ + 1)).filter (fun d => Nat.Coprime d K.natAbs),
    (sieveWeight (X ^ ρ₁) (X ^ ((1 : ℝ) / 5)) false 2 d : ℂ) *
    ∑ ℓ ∈ (range (⌊X ^ (0.9 : ℝ)⌋₊ + 1)).filter
        (fun ℓ => Nat.gcd ℓ K.natAbs = Int.gcd (c - 1) K ∧ Nat.Coprime ℓ d),
      g ℓ * ((∑ n ∈ M.filter (fun n : ℕ => (∃ p : ℕ, p.Prime ∧ K * n + c = ℓ * p + 1) ∧
              (d : ℤ) ∣ K * n + c), ω n) -
        (1 / (Nat.totient d : ℂ)) *
          ((K : ℂ) / (Nat.totient (K.natAbs / Int.gcd (c - 1) K) : ℂ)) *
          ∑ n ∈ M, ω n / ((ℓ : ℂ) * (Real.log ((K : ℝ) * n / ℓ) : ℂ)))

/-- The second sum of Hypothesis 6.4, page 22: lower semilinear sieve weights of level
`X^{ρ₂}` and sifting parameter `X^{1/σ}`, primes `L(n)` with `L(n) ≡ 1 (mod d)`. -/
noncomputable def semDisc (ρ₂ σ X : ℝ) (K c : ℤ) (M : Finset ℕ) (ω : ℕ → ℂ) : ℂ :=
  ∑ d ∈ (range (⌊X ^ ρ₂⌋₊ + 1)).filter (fun d => Nat.Coprime d K.natAbs),
    (sieveWeight (X ^ ρ₂) (X ^ (1 / σ)) true 1 d : ℂ) *
      ((∑ n ∈ M.filter (fun n : ℕ => 0 < K * n + c ∧ (K * n + c).toNat.Prime ∧
              (d : ℤ) ∣ K * n + c - 1), ω n) -
        (1 / (Nat.totient d : ℂ)) * ((K : ℂ) / (Nat.totient K.natAbs : ℂ)) *
          ∑ n ∈ M, ω n / (Real.log ((K : ℝ) * n) : ℂ))

/-- Hypothesis 6.4, page 22, for the weights `ω` on `M`, with the implied bound written as an
explicit bound `B`, uniform over all `g` of convolution type. -/
def Hyp64 (ρ₁ ρ₂ σ X : ℝ) (K c : ℤ) (M : Finset ℕ) (ω : ℕ → ℂ) (B : ℝ) : Prop :=
  (∀ g, ConvType X σ g → ‖linDisc ρ₁ X K c M ω g‖ ≤ B) ∧ ‖semDisc ρ₂ σ X K c M ω‖ ≤ B

/-! ### The linearity step: (2.2) and Hypothesis 6.4 for `e(ξ m)` give it for `ω_m` -/

theorem linDisc_add (ρ₁ X : ℝ) (K c : ℤ) (M : Finset ℕ) (ω₁ ω₂ : ℕ → ℂ) (g : ℕ → ℂ) :
    linDisc ρ₁ X K c M (fun n => ω₁ n + ω₂ n) g =
      linDisc ρ₁ X K c M ω₁ g + linDisc ρ₁ X K c M ω₂ g := by
  unfold linDisc
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun ℓ _ => ?_)
  simp only [Finset.sum_add_distrib, add_div]
  ring

theorem linDisc_smul (ρ₁ X : ℝ) (K c : ℤ) (M : Finset ℕ) (a : ℂ) (ω : ℕ → ℂ) (g : ℕ → ℂ) :
    linDisc ρ₁ X K c M (fun n => a * ω n) g = a * linDisc ρ₁ X K c M ω g := by
  unfold linDisc
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have hh : ∀ (T : Finset ℕ) (f : ℕ → ℂ), ∑ n ∈ T, a * f n = a * ∑ n ∈ T, f n :=
    fun T f => (Finset.mul_sum T f a).symm
  simp only [mul_div_assoc, hh]
  rw [mul_left_comm a, Finset.mul_sum _ _ a]
  congr 1
  refine Finset.sum_congr rfl (fun ℓ _ => ?_)
  ring

theorem semDisc_add (ρ₂ σ X : ℝ) (K c : ℤ) (M : Finset ℕ) (ω₁ ω₂ : ℕ → ℂ) :
    semDisc ρ₂ σ X K c M (fun n => ω₁ n + ω₂ n) =
      semDisc ρ₂ σ X K c M ω₁ + semDisc ρ₂ σ X K c M ω₂ := by
  unfold semDisc
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  simp only [Finset.sum_add_distrib, add_div]
  ring

theorem semDisc_smul (ρ₂ σ X : ℝ) (K c : ℤ) (M : Finset ℕ) (a : ℂ) (ω : ℕ → ℂ) :
    semDisc ρ₂ σ X K c M (fun n => a * ω n) = a * semDisc ρ₂ σ X K c M ω := by
  unfold semDisc
  rw [Finset.mul_sum]
  have hh : ∀ (T : Finset ℕ) (f : ℕ → ℂ), ∑ n ∈ T, a * f n = a * ∑ n ∈ T, f n :=
    fun T f => (Finset.mul_sum T f a).symm
  refine Finset.sum_congr rfl (fun d _ => ?_)
  simp only [mul_div_assoc, hh]
  ring

theorem linDisc_sum {ι : Type*} (s : Finset ι) (ρ₁ X : ℝ) (K c : ℤ) (M : Finset ℕ)
    (a : ι → ℂ) (ω : ι → ℕ → ℂ) (g : ℕ → ℂ) :
    linDisc ρ₁ X K c M (fun n => ∑ i ∈ s, a i * ω i n) g =
      ∑ i ∈ s, a i * linDisc ρ₁ X K c M (ω i) g := by
  induction s using Finset.induction_on with
  | empty =>
    have h := linDisc_smul ρ₁ X K c M 0 (fun _ => 0) g
    simpa using h
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [linDisc_add, linDisc_smul, ih]

theorem semDisc_sum {ι : Type*} (s : Finset ι) (ρ₂ σ X : ℝ) (K c : ℤ) (M : Finset ℕ)
    (a : ι → ℂ) (ω : ι → ℕ → ℂ) :
    semDisc ρ₂ σ X K c M (fun n => ∑ i ∈ s, a i * ω i n) =
      ∑ i ∈ s, a i * semDisc ρ₂ σ X K c M (ω i) := by
  induction s using Finset.induction_on with
  | empty =>
    have h := semDisc_smul ρ₂ σ X K c M 0 (fun _ => 0)
    simpa using h
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [semDisc_add, semDisc_smul, ih]

/-- The linearity step on page 30: Hypothesis 6.4 for each `ω_i` with bound `B` gives it for
`∑ a_i ω_i` with bound `(∑ |a_i|) B`. -/
theorem hyp64_combo {ι : Type*} (s : Finset ι) (ρ₁ ρ₂ σ X : ℝ) (K c : ℤ) (M : Finset ℕ)
    (a : ι → ℂ) (ω : ι → ℕ → ℂ) (B : ℝ) (h : ∀ i ∈ s, Hyp64 ρ₁ ρ₂ σ X K c M (ω i) B) :
    Hyp64 ρ₁ ρ₂ σ X K c M (fun n => ∑ i ∈ s, a i * ω i n) ((∑ i ∈ s, ‖a i‖) * B) := by
  refine ⟨fun g hg => ?_, ?_⟩
  · rw [linDisc_sum, Finset.sum_mul]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun i hi => ?_))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((h i hi).1 g hg) (norm_nonneg _)
  · rw [semDisc_sum, Finset.sum_mul]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun i hi => ?_))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (h i hi).2 (norm_nonneg _)

theorem d71_eC_add (x y : ℝ) : eC (x + y) = eC x * eC y := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem d71_eC_norm (x : ℝ) : ‖eC x‖ = 1 := by
  simp [eC, Complex.norm_exp]

/-! ### The LEAFs -/

/-- The conclusion of Theorem 6.5, page 22, together with its hypothesis, on a range `M` of
consecutive integers in `(X - 1, 2 X]` that plays `n ∼ N`, with `N` written `X`; the parameters
are those of (7.2) with `ε = η`, for which `H(ρ₁, ρ₂, σ)` holds by page 22 once `η` is small.
The error `O(X^{1/2})` is weakened to `ε X` inside the bracket, and the bound of Hypothesis 6.4 is
`ε X (log X)^{-100}` as in the remark closing Section 7, page 30. -/
def Thm65Range : Prop :=
  ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
    ∀ (E : ℕ) (Kc Cω ε : ℝ), 0 < ε → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    ∀ K c : ℤ, Amenable K c → (K : ℝ) ≤ Kc * Real.log X ^ E →
    ∀ M : Finset ℕ, (∀ m ∈ M, X - 1 < m ∧ (m : ℝ) ≤ 2 * X) →
      (∀ m₁ ∈ M, ∀ m₂ ∈ M, ∀ m : ℕ, m₁ ≤ m → m ≤ m₂ → m ∈ M) →
    ∀ ω : ℕ → ℝ, (∀ m, 0 ≤ ω m) → (∀ m, ω m ≤ Cω) →
    Hyp64 (1 / 2 - 10 * η) (3 / 7 - 10 * η) (3 + η) X K c M (fun m => (ω m : ℂ))
      (ε * X / Real.log X ^ 100) →
    δ₀ * singularS K c * (∑ m ∈ M, ω m - ε * X) ≤
      Real.log X ^ ((3 : ℝ) / 2) * ∑ m ∈ M.filter (fun m : ℕ => Good (K * m + c)), ω m

/-- Hypothesis 6.4 for `(e(ξ m))_m` with `ξ = Q α` as in (7.3), page 30, for `α` one frequency
with the approximation of Lemma 7.1, `L(m) = Q W m + W c₀ + b`, `x = N/(3Q)`, the parameters
(7.2), and the bound `x (log x)^{-199}`, weaker than the `x (log x)^{-200}` of page 30. The
range `M` plays `m ∼ x`. -/
def Hyp64Exp : Prop :=
  ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η : ℝ, 0 < η → η ≤ η₁ → ∀ Cc : ℕ, ∃ A : ℕ, ∀ J w : ℕ, 5 ≤ J →
    wBig ≤ w → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Q : ℕ, 1 ≤ Q →
    (Q : ℝ) ≤ Real.log N ^ (A * (3 * Cc) ^ Cc) →
    ∀ α : ℝ, Lemma71Adapted (fun _ : Fin 1 => α) (WW J w) N (A * (3 * Cc) ^ Cc) A Q →
    ∀ b : ℤ, Amenable (WW J w) b → ∀ c₀ ∈ QRes Q (WW J w) b,
    ∀ M : Finset ℕ, (∀ m ∈ M, (N : ℝ) / (3 * Q) - 1 < m ∧ (m : ℝ) ≤ 2 * ((N : ℝ) / (3 * Q))) →
      (∀ m₁ ∈ M, ∀ m₂ ∈ M, ∀ m : ℕ, m₁ ≤ m → m ≤ m₂ → m ∈ M) →
    Hyp64 (1 / 2 - 10 * η) (3 / 7 - 10 * η) (3 + η) ((N : ℝ) / (3 * Q)) ((Q : ℤ) * WW J w)
      (WW J w * c₀ + b) M (fun m => eC (-((Q : ℝ) * α) * m))
      (((N : ℝ) / (3 * Q)) / Real.log ((N : ℝ) / (3 * Q)) ^ 199)

/-- LEAF: Theorem 6.5, page 22, the weighted sieve lower bound under Hypothesis 6.4, read on a
range of consecutive integers; the proof is pages 23 to 28, with the semilinear sieve and the
condition `H(1/2 - ε, 3/7 - ε, 3 + ε)`. The remark on page 11 claims the range generalization.
Class HARD. -/
theorem thm65_range : Thm65Range := by sorry

/-- LEAF: Hypothesis 6.4 for `e(ξ m)` with `ξ` as in (7.3), page 30, proved in Section 10:
major arcs in Subsections 10.1 to 10.3, minor arcs in Subsections 10.4 and 10.5, from Lemmas 8.1,
8.2, 9.1 and 9.2. Class HARD. -/
theorem hyp64_exp : Hyp64Exp := by sorry

/-- `L(m) = Q W m + W c₀ + b` is amenable, page 30, from the amenability of `W n + b` and
`c₀ ∈ 𝒬` of (5.1). -/
theorem amenable_QW (W b : ℤ) (Q : ℕ) (c₀ : ℕ) (hA : Amenable W b) (hQ : 1 ≤ Q)
    (hc : c₀ ∈ QRes Q W b) : Amenable ((Q : ℤ) * W) (W * c₀ + b) := by
  obtain ⟨hW1, h216, hcop, hp, j, t, h, hb, h3, hD⟩ := hA
  obtain ⟨-, hcQ, hpQ⟩ := Finset.mem_filter.mp hc
  have hQ1 : (1 : ℤ) ≤ Q := by exact_mod_cast hQ
  refine ⟨by nlinarith, dvd_mul_of_dvd_right h216 _, ?_, ?_, ?_⟩
  · refine IsCoprime.mul_right hcQ ?_
    have := hcop.add_mul_left_left c₀
    rwa [add_comm] at this
  · intro p hpr hp4 hp3 hpd hdiv
    rcases (Nat.prime_iff_prime_int.mp hpr).dvd_or_dvd hpd with hq | hw
    · exact hpQ p hpr hp4 hp3 (Int.natCast_dvd_natCast.mp hq) hdiv
    · apply hp p hpr hp4 hp3 hw
      have : (p : ℤ) ∣ (W * c₀ + b - 1) - W * c₀ := dvd_sub hdiv (dvd_mul_of_dvd_left hw _)
      rwa [show W * (c₀ : ℤ) + b - 1 - W * c₀ = b - 1 by ring] at this
  · obtain ⟨k, hk⟩ := hD
    refine ⟨j, t, h + 3 * k * c₀, ?_, ?_, dvd_mul_of_dvd_right ⟨k, hk⟩ _⟩
    · have : W * c₀ + b - 1 = W * c₀ + (b - 1) := by ring
      rw [this, hb, hk]
      ring
    · intro h3'
      apply h3
      have : (4 * h + 1) = (4 * (h + 3 * k * c₀) + 1) - 3 * (4 * k * c₀) := by ring
      rw [this]
      exact dvd_sub h3' (dvd_mul_right _ _)

/-! ### The deduction of display (7.1) -/

/-- The shape of the ranges `n ∼ N/3` and `N/3 < n < N/2`: inside `[N/3, 2N/3)` and convex. -/
def RShape (R : ℕ → Finset ℕ) : Prop :=
  (∀ N n, n ∈ R N → (N : ℝ) / 3 ≤ n ∧ (n : ℝ) < 2 * N / 3) ∧
    ∀ N n₁ n₂ n, n₁ ∈ R N → n₂ ∈ R N → n₁ ≤ n → n ≤ n₂ → n ∈ R N

/-- The scale step: for `N` large and `Q ≤ (log N)^B`, `x = N/(3Q)` is large,
`Q W ≤ 3^B W (log x)^B`, and `C² x (log x)^{-199} ≤ ε x (log x)^{-100}`. -/
theorem d71_scale (B : ℕ) (W : ℤ) (hW : 1 ≤ W) (Y C ε : ℝ) (hε : 0 < ε) :
    ∃ N₂ : ℕ, ∀ N : ℕ, N₂ ≤ N → ∀ Q : ℕ, 1 ≤ Q → (Q : ℝ) ≤ Real.log N ^ B →
      Y ≤ (N : ℝ) / (3 * Q) ∧
      (((Q : ℤ) * W : ℤ) : ℝ) ≤ ((W : ℝ) * 3 ^ B) * Real.log ((N : ℝ) / (3 * Q)) ^ B ∧
      C * ((N : ℝ) / (3 * Q) / Real.log ((N : ℝ) / (3 * Q)) ^ 199) ≤
        ε * ((N : ℝ) / (3 * Q)) / Real.log ((N : ℝ) / (3 * Q)) ^ 100 := by
  obtain ⟨N₃, H3⟩ := eventually_log_rpow_le_sqrt 3 (B : ℝ)
  set L : ℝ := max 1 (|C| / ε) with hL
  set Y' : ℝ := max Y (max 9 (Real.exp L)) with hY'
  have hY'0 : 0 ≤ Y' := le_trans (by norm_num) (le_trans (le_max_left 9 _) (le_max_right _ _))
  refine ⟨max N₃ (⌈Y' ^ 2⌉₊ + 1), ?_⟩
  intro N hN Q hQ hQB
  have hN3 : N₃ ≤ N := le_trans (le_max_left _ _) hN
  have hNY : ⌈Y' ^ 2⌉₊ + 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNr : Y' ^ 2 ≤ (N : ℝ) := by
    have h1 : Y' ^ 2 ≤ (⌈Y' ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Y' ^ 2⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : ⌈Y' ^ 2⌉₊ ≤ N)
    linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have e3 := H3 N hN3
  rw [Real.rpow_natCast] at e3
  have h3Q : 3 * (Q : ℝ) ≤ Real.sqrt N := by linarith
  have hsq0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
  have hX : Real.sqrt N ≤ (N : ℝ) / (3 * Q) := by
    rw [le_div_iff₀ (by positivity)]
    have := Real.mul_self_sqrt (show (0 : ℝ) ≤ N by linarith)
    nlinarith
  have hYs : Y' ≤ Real.sqrt N := Real.le_sqrt_of_sq_le hNr
  have hXY : Y' ≤ (N : ℝ) / (3 * Q) := le_trans hYs hX
  set X : ℝ := (N : ℝ) / (3 * Q) with hXdef
  have hX9 : 9 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hXY
  have hXe : Real.exp L ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hXY
  have hlogL : L ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hXe
  have hl1 : 1 ≤ Real.log X := le_trans (le_max_left _ _) hlogL
  refine ⟨le_trans (le_max_left _ _) hXY, ?_, ?_⟩
  · have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
    have hlogN : Real.log N ≤ 3 * Real.log X := by
      have h1 : Real.log N = 2 * Real.log (Real.sqrt N) := by
        rw [Real.log_sqrt (by linarith)]; ring
      have h2 : Real.log (Real.sqrt N) ≤ Real.log X := Real.log_le_log hsq0 hX
      linarith
    have hp : Real.log N ^ B ≤ (3 * Real.log X) ^ B := pow_le_pow_left₀ hlogN0 hlogN B
    rw [mul_pow] at hp
    have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
    push_cast
    calc (Q : ℝ) * W ≤ Real.log N ^ B * W := mul_le_mul_of_nonneg_right hQB (by linarith)
      _ ≤ 3 ^ B * Real.log X ^ B * W := mul_le_mul_of_nonneg_right hp (by linarith)
      _ = W * 3 ^ B * Real.log X ^ B := by ring
  · have hX0 : 0 < X := by linarith
    set l : ℝ := Real.log X with hl
    have hl0 : 0 < l := by linarith
    have h99 : l ≤ l ^ 99 := by
      calc l = l ^ 1 := (pow_one l).symm
        _ ≤ l ^ 99 := pow_le_pow_right₀ hl1 (by norm_num)
    have hCl : |C| / ε ≤ l ^ 99 := le_trans (le_trans (le_max_right _ _) hlogL) h99
    have hC : |C| ≤ ε * l ^ 99 := by
      rw [div_le_iff₀ hε] at hCl; linarith
    have hsplit : l ^ 199 = l ^ 99 * l ^ 100 := by rw [← pow_add]
    rw [hsplit, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have hCC : C ≤ |C| := le_abs_self C
    have hpos : 0 ≤ X * l ^ 100 := by positivity
    calc C * X * l ^ 100 = C * (X * l ^ 100) := by ring
      _ ≤ (ε * l ^ 99) * (X * l ^ 100) := mul_le_mul_of_nonneg_right (le_trans hCC hC) hpos
      _ = ε * X * (l ^ 99 * l ^ 100) := by ring

theorem d71_image_bounds (R : ℕ → Finset ℕ) (hR : RShape R) (N Q c₀ : ℕ) (hQ : 1 ≤ Q)
    (hc : c₀ < Q) :
    (∀ m ∈ ((R N).filter (fun n => n % Q = c₀)).image (fun n => n / Q),
        (N : ℝ) / (3 * Q) - 1 < m ∧ (m : ℝ) ≤ 2 * ((N : ℝ) / (3 * Q))) ∧
      (∀ m₁ ∈ ((R N).filter (fun n => n % Q = c₀)).image (fun n => n / Q),
        ∀ m₂ ∈ ((R N).filter (fun n => n % Q = c₀)).image (fun n => n / Q),
        ∀ m : ℕ, m₁ ≤ m → m ≤ m₂ →
          m ∈ ((R N).filter (fun n => n % Q = c₀)).image (fun n => n / Q)) := by
  have hQ0 : 0 < Q := hQ
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ0
  constructor
  · intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hnR, hmod⟩ := Finset.mem_filter.mp hn
    obtain ⟨h1, h2⟩ := hR.1 N n hnR
    have e := Nat.div_add_mod n Q
    rw [hmod] at e
    have er : (n : ℝ) = Q * ((n / Q : ℕ) : ℝ) + c₀ := by exact_mod_cast e.symm
    have hcr : (c₀ : ℝ) + 1 ≤ Q := by exact_mod_cast hc
    have hc0 : (0 : ℝ) ≤ c₀ := by positivity
    constructor
    · rw [sub_lt_iff_lt_add, div_lt_iff₀ (by positivity)]
      nlinarith
    · rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      nlinarith
  · intro m₁ hm₁ m₂ hm₂ m hle hle'
    obtain ⟨n₁, hn₁, rfl⟩ := Finset.mem_image.mp hm₁
    obtain ⟨n₂, hn₂, rfl⟩ := Finset.mem_image.mp hm₂
    obtain ⟨hR₁, hmod₁⟩ := Finset.mem_filter.mp hn₁
    obtain ⟨hR₂, hmod₂⟩ := Finset.mem_filter.mp hn₂
    have e₁ := Nat.div_add_mod n₁ Q
    have e₂ := Nat.div_add_mod n₂ Q
    refine Finset.mem_image.mpr ⟨Q * m + c₀, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · refine hR.2 N n₁ n₂ _ hR₁ hR₂ ?_ ?_
      · have := Nat.mul_le_mul_left Q hle
        omega
      · have := Nat.mul_le_mul_left Q hle'
        omega
    · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc]
    · rw [Nat.mul_add_div hQ0, Nat.div_eq_of_lt hc, add_zero]

theorem d71_reindex (S : Finset ℕ) (Q c₀ : ℕ) (hc : c₀ < Q) (f : ℕ → ℝ) :
    ∑ m ∈ (S.filter (fun n => n % Q = c₀)).image (fun n => n / Q), f (Q * m + c₀) =
      ∑ n ∈ S.filter (fun n => n % Q = c₀), f n := by
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl (fun n hn => ?_)
    have h := (Finset.mem_filter.mp hn).2
    congr 1
    have := Nat.div_add_mod n Q
    omega
  · intro x hx y hy hxy
    have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
    have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
    have e1 := Nat.div_add_mod x Q
    have e2 := Nat.div_add_mod y Q
    simp only at hxy
    rw [← e1, ← e2, h1, h2, hxy]

/-- Display (7.1) on `R` from Theorem 6.5, Hypothesis 6.4 for `e(ξ m)` and the amenability of
`L`: the deduction on page 30. -/
theorem display71On_of_leaves (R : ℕ → Finset ℕ) (hR : RShape R) (hT : Thm65Range)
    (hH : Hyp64Exp)
    (hAm : ∀ (W b : ℤ) (Q c₀ : ℕ), Amenable W b → 1 ≤ Q → c₀ ∈ QRes Q W b →
      Amenable ((Q : ℤ) * W) (W * c₀ + b)) : Display71On R := by
  obtain ⟨δ₀, hδ₀, η₀, hη₀, T⟩ := hT
  obtain ⟨η₁, hη₁, H⟩ := hH
  set η : ℝ := min η₀ η₁ with hη
  have hη0 : 0 < η := lt_min hη₀ hη₁
  refine ⟨δ₀, hδ₀, fun Cc => ?_⟩
  obtain ⟨A, HA⟩ := H η hη0 (min_le_right _ _) Cc
  refine ⟨A, ?_⟩
  intro J w hJ hw hCw ε hε
  set B : ℕ := A * (3 * Cc) ^ Cc with hB
  set W : ℤ := WW J w with hWdef
  have hW1 : (1 : ℤ) ≤ W := WW_pos' J w
  obtain ⟨N₁, HN1⟩ := HA J w hJ hw
  obtain ⟨X₀, HX⟩ := T η hη0 (min_le_left _ _) B ((W : ℝ) * 3 ^ B) ((Cc : ℝ) * Cc) (3 * ε)
    (by positivity)
  obtain ⟨N₂, HN2⟩ := d71_scale B W hW1 (max X₀ 1) ((Cc : ℝ) * Cc) (3 * ε) (by positivity)
  refine ⟨max N₁ N₂, ?_⟩
  intro χ hχ0 c α hc hrep N hN Q hQ1 hQB hAd b hb0 hbW hamen t ht c₀ hc₀
  have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : N₂ ≤ N := le_trans (le_max_right _ _) hN
  have hc₀Q : c₀ < Q := by
    have := (Finset.mem_filter.mp hc₀).1
    exact Finset.mem_range.mp this
  obtain ⟨hXY', hK, hBd⟩ := HN2 N hN2 Q hQ1 hQB
  have hXY := le_trans (le_max_left _ _) hXY'
  have hX1 := le_trans (le_max_right _ _) hXY'
  set X : ℝ := (N : ℝ) / (3 * Q) with hX
  set M : Finset ℕ := ((R N).filter (fun n => n % Q = c₀)).image (fun n => n / Q) with hM
  obtain ⟨hMb, hMc⟩ := d71_image_bounds R hR N Q c₀ hQ1 hc₀Q
  set ω : ℕ → ℝ := fun m => χ (t - ((Q * m + c₀ : ℕ) : ℤ)) with hω
  -- the bound `|χ| ≤ C²`
  have hχC : ∀ n : ℤ, χ n ≤ (Cc : ℝ) * Cc := by
    intro n
    have h1 : ‖(χ n : ℂ)‖ ≤ ∑ k, ‖c k * eC (α k * n)‖ := by
      rw [hrep n]; exact norm_sum_le _ _
    have h2 : ∑ k, ‖c k * eC (α k * n)‖ ≤ ∑ _k : Fin Cc, (Cc : ℝ) := by
      refine Finset.sum_le_sum (fun k _ => ?_)
      rw [norm_mul, d71_eC_norm, mul_one]; exact hc k
    have h3 : ∑ _k : Fin Cc, (Cc : ℝ) = (Cc : ℝ) * Cc := by simp
    have h4 : χ n ≤ ‖(χ n : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
    linarith
  -- the expansion of `ω_m` by (2.2)
  have hωexp : ∀ m : ℕ, ((ω m : ℝ) : ℂ) =
      ∑ k, (c k * eC (α k * ((t : ℝ) - c₀))) * eC (-((Q : ℝ) * α k) * m) := by
    intro m
    simp only [hω]
    rw [hrep]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [mul_assoc, ← d71_eC_add]
    congr 2
    push_cast
    ring
  -- Hypothesis 6.4 for `ω`
  have hHyp : Hyp64 (1 / 2 - 10 * η) (3 / 7 - 10 * η) (3 + η) X ((Q : ℤ) * W) (W * c₀ + b) M
      (fun m => (ω m : ℂ)) (3 * ε * X / Real.log X ^ 100) := by
    have hcombo := hyp64_combo Finset.univ (1 / 2 - 10 * η) (3 / 7 - 10 * η) (3 + η) X
      ((Q : ℤ) * W) (W * c₀ + b) M (fun k => c k * eC (α k * ((t : ℝ) - c₀)))
      (fun k m => eC (-((Q : ℝ) * α k) * m)) (X / Real.log X ^ 199)
      (fun k _ => HN1 N hN1 Q hQ1 hQB (α k) (fun _ => hAd k) b hamen c₀ hc₀ M hMb hMc)
    have hfun : (fun m => (ω m : ℂ)) = (fun n : ℕ => ∑ k, (c k * eC (α k * ((t : ℝ) - c₀))) *
        eC (-((Q : ℝ) * α k) * n)) := funext hωexp
    have hsum : (∑ k, ‖c k * eC (α k * ((t : ℝ) - c₀))‖) ≤ (Cc : ℝ) * Cc := by
      have : ∑ k, ‖c k * eC (α k * ((t : ℝ) - c₀))‖ ≤ ∑ _k : Fin Cc, (Cc : ℝ) := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        rw [norm_mul, d71_eC_norm, mul_one]; exact hc k
      simpa using this
    have hX0 : 0 ≤ X / Real.log X ^ 199 := by
      have := Real.log_nonneg hX1
      positivity
    rw [hfun]
    refine ⟨fun g hg => le_trans (hcombo.1 g hg) ?_, le_trans hcombo.2 ?_⟩
    · exact le_trans (mul_le_mul_of_nonneg_right hsum hX0) hBd
    · exact le_trans (mul_le_mul_of_nonneg_right hsum hX0) hBd
  have hmain := HX X hXY ((Q : ℤ) * W) (W * c₀ + b) (hAm W b Q c₀ hamen hQ1 hc₀) hK M hMb hMc
    ω (fun m => hχ0 _) (fun m => hχC _) hHyp
  -- reindexing
  have e1 : ∑ m ∈ M, ω m = ∑ n ∈ (R N).filter (fun n => n % Q = c₀), χ (t - n) := by
    have := d71_reindex (R N) Q c₀ hc₀Q (fun n => χ (t - n))
    simpa [hω, hM] using this
  have e2 : ∑ m ∈ M.filter (fun m : ℕ => Good ((Q : ℤ) * W * m + (W * c₀ + b))), ω m =
      ∑ n ∈ ((R N).filter (fun n : ℕ => Good (W * (n : ℤ) + b))).filter
        (fun n => n % Q = c₀), χ (t - n) := by
    rw [Finset.filter_comm, Finset.sum_filter, Finset.sum_filter]
    have := d71_reindex (R N) Q c₀ hc₀Q
      (fun n => if Good (W * (n : ℤ) + b) then χ (t - n) else 0)
    rw [← this, hM]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have harg : (Q : ℤ) * W * m + (W * c₀ + b) = W * (((Q * m + c₀ : ℕ)) : ℤ) + b := by
      push_cast; ring
    simp only [hω, harg]
  have e3 : 3 * ε * X = ε * N / Q := by
    rw [hX]; field_simp
  rw [e2, e1, e3] at hmain
  exact hmain

theorem rshape_dyad : RShape dyad := by
  refine ⟨fun N n hn => ?_, fun N n₁ n₂ n h₁ h₂ hle hle' => ?_⟩
  · unfold dyad at hn
    exact (Finset.mem_filter.mp hn).2
  · unfold dyad at *
    rw [Finset.mem_filter] at *
    have h1 : ((n₁ : ℕ) : ℝ) ≤ n := by exact_mod_cast hle
    have h2 : ((n : ℕ) : ℝ) ≤ n₂ := by exact_mod_cast hle'
    refine ⟨Finset.mem_range.mpr (lt_of_le_of_lt hle' (Finset.mem_range.mp h₂.1)), ?_, ?_⟩
    · linarith [h₁.2.1]
    · linarith [h₂.2.2]

theorem rshape_half : RShape half := by
  refine ⟨fun N n hn => ?_, fun N n₁ n₂ n h₁ h₂ hle hle' => ?_⟩
  · unfold half at hn
    have h := (Finset.mem_filter.mp hn).2
    have hN : (0 : ℝ) ≤ N := by positivity
    exact ⟨h.1.le, by linarith [h.2]⟩
  · unfold half at *
    rw [Finset.mem_filter] at *
    have h1 : ((n₁ : ℕ) : ℝ) ≤ n := by exact_mod_cast hle
    have h2 : ((n : ℕ) : ℝ) ≤ n₂ := by exact_mod_cast hle'
    refine ⟨Finset.mem_range.mpr (lt_of_le_of_lt hle' (Finset.mem_range.mp h₂.1)), ?_, ?_⟩
    · linarith [h₁.2.1]
    · linarith [h₂.2.2]

/-- Display (7.1) for `n ∼ N/3`, the statement of `display71_dyad`, from the leaves. -/
theorem display71_dyad_of_leaves : type_of% @LeanLab.Teravainen2016.display71_dyad :=
  display71On_of_leaves dyad rshape_dyad thm65_range hyp64_exp
    (fun W b Q c₀ hA hQ hc => amenable_QW W b Q c₀ hA hQ hc)

/-- Display (7.1) for `N/3 < n < N/2`, the statement of `display71_half`, from the leaves. -/
theorem display71_half_of_leaves : type_of% @LeanLab.Teravainen2016.display71_half :=
  display71On_of_leaves half rshape_half thm65_range hyp64_exp
    (fun W b Q c₀ hA hQ hc => amenable_QW W b Q c₀ hA hQ hc)

end LeanLab.Teravainen2016

#print axioms LeanLab.Teravainen2016.display71_dyad_of_leaves
#print axioms LeanLab.Teravainen2016.display71_half_of_leaves
#print axioms LeanLab.Teravainen2016.hyp64_combo
#print axioms LeanLab.Teravainen2016.display71On_of_leaves
