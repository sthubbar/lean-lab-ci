/-
P0069 pages 50 to 52. The analytic parents for the explicit lower short weight.
The sealed coefficient declarations now live in Decomp514a with identical text.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp514a

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d
open scoped BigOperators
set_option maxHeartbeats 400000

/-! ### The analytic leaves -/

/-- LEAF, CITED-LEFT. P0069 Baker Harman Pintz 1997, Section 5, page 51, display 5.17, "a
straightforward consequence of the prime number theorem, with error term `Y exp(-ε L^(1/2))`",
with the U-1624 factor, so the density is the constant `v0 / log Y`, summed from the left end
of J. This is the cited input of 5.17 with no character: the prime number theorem with error
term, applied to the prime term and, through the Buchstab identity, to the E2 and E4 sums of
5.15. Its truth also needs the numerical fact, U-1624, that the clipping of `lowerFactor` is
inactive on J for large `x`; see the QUESTION in the burst 7 notes. -/
theorem lower_principal_density (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((lowerShortWeight ω ε x m : ℂ) - lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- P0069 Baker Harman Pintz 1997, Section 5, page 51, display 5.17 in the form condition iii
of Theorem 2, display 1.8 on page 3, takes for the principal character. The prime factors of
every term exceed `Z ^ c1`, so the principal character modulo `q ≤ L^A` is one on the support
for large `x`, by `rawLower_coprime`; the rest is the cited 5.17, `lower_principal_density`. -/
theorem lower_principal_distribution (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((lowerShortWeight ω ε x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q) -
            lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C0, hC0⟩ := lower_principal_density ω hω hz hε hε8 A hA
  obtain ⟨C1, hC1⟩ := log_rpow_lt_rpow A
  refine ⟨max (max C0 C1) 1, fun x hx q hq hqA t ht => ?_⟩
  have hx0 : C0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx1 : C1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxone : 1 ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hZc, hZ1⟩ := scaleZ_rpow_ge hε hε8 hxone
  have hlt := hC1 x hx1
  have hqZ : (q : ℝ) < scaleZ ε x ^ ((1+7*(2*(1/16-1/10^5)))/15-ε) := by linarith
  have hsum : ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
      ((lowerShortWeight ω ε x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q) -
        lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε))) =
      ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
      ((lowerShortWeight ω ε x m : ℂ) - lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε))) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    by_cases h0 : rawLower ε x m = 0
    · simp [lowerShortWeight, h0]
    · have hmJ := (Finset.mem_filter.mp hm).1
      unfold rightInterval at hmJ
      have hmY : ⌊x ^ (11 / 20 + ε)⌋₊ < m := (Finset.mem_Ioc.mp hmJ).1
      have hYm : x ^ (11 / 20 + ε) < (m : ℝ) := by
        have := Nat.lt_floor_add_one (x ^ (11 / 20 + ε))
        have h' : ((⌊x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hmY
        linarith
      have hxY : x ^ (11 / 200 : ℝ) ≤ x ^ (11 / 20 + ε) :=
        Real.rpow_le_rpow_of_exponent_le hxone (by linarith)
      have hqm : q < m := by
        have : (q : ℝ) < m := by linarith
        exact_mod_cast this
      have hcop := rawLower_coprime hZ1 hq hqm hqZ h0
      have hu : IsUnit (m : ZMod q) := (ZMod.isUnit_iff_coprime m q).mpr hcop
      rw [MulChar.one_apply hu, mul_one]
  rw [hsum]
  have hY : 0 ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
    have := Real.rpow_nonneg (by linarith : (0:ℝ) ≤ x) (11 / 20 + ε)
    have hl : 0 ≤ Real.log x := Real.log_nonneg hxone
    have := Real.rpow_nonneg hl (-A)
    positivity
  calc _ ≤ C0 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := hC0 x hx0 t ht
    _ ≤ max (max C0 C1) 1 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _)) hY

/-- LEAF, CITED-LEFT. P0069 Baker Harman Pintz 1997, Section 5, page 51, display 5.17 and page
3, display 1.8, the non-principal characters, for the three terms of 5.15 one at a time: the
prime term, the E2 sum over `p1 p2 n3` and the E4 sum over `p1 p2 p3 p4 n5`, each times the
U-1624 factor. This is the Siegel-Walfisz form of the prime number theorem used for 5.17,
with partial summation against the slowly varying factor, applied to each term of 5.15 whose
rough factors have no prime factor below `Z ^ c1`. -/
theorem lower_nonprincipal_terms (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((lowerFactor ω ε x m * primeWeight m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) ∧
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((lowerFactor ω ε x m * lowerTwoTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) ∧
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((lowerFactor ω ε x m * lowerFourTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q)‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C1, h1⟩ := Decomp514a.leaf_nonprincipal_prime ω hω hz hε hε8 A hA
  obtain ⟨C2, h2⟩ := Decomp514a.leaf_nonprincipal_two_rough ω hω hz hε hε8 A hA
  obtain ⟨C3, h3⟩ := Decomp514a.leaf_nonprincipal_four_rough ω hω hz hε hε8 A hA
  let C := max (max C1 C2) (max C3 1)
  have hC1 : C1 ≤ C := (le_max_left C1 C2).trans (le_max_left _ _)
  have hC2 : C2 ≤ C := (le_max_right C1 C2).trans (le_max_left _ _)
  have hC3 : C3 ≤ C := (le_max_left C3 1).trans (le_max_right _ _)
  have hCone : 1 ≤ C := (le_max_right C3 1).trans (le_max_right _ _)
  refine ⟨C, fun x hx q hq hqA χ hχ t ht => ?_⟩
  have hx1 : 1 ≤ x := hCone.trans hx
  have hscale : 0 ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (Real.rpow_nonneg (Real.log_nonneg hx1) _)
  have liftBound {v c : ℝ} (hc : c ≤ C)
      (hv : v ≤ c * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :
      v ≤ C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
    calc v ≤ c * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := hv
      _ ≤ C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc hscale
  exact ⟨liftBound hC1 (h1 x (hC1.trans hx) q hq hqA χ hχ t ht),
    liftBound hC2 (h2 x (hC2.trans hx) q hq hqA χ hχ t ht),
    liftBound hC3 (h3 x (hC3.trans hx) q hq hqA χ hχ t ht)⟩

/-- P0069 Baker Harman Pintz 1997, Section 5, page 51, display 5.17 and page 3,
display 1.8, the non-principal characters: here `δχ = 0`. By linearity of 5.15, b0 is the
factor times the prime term minus the E2 and E4 sums, and each piece is the cited
Siegel-Walfisz input `lower_nonprincipal_terms`. -/
theorem lower_nonprincipal_distribution (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q))‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C0, hC0⟩ := lower_nonprincipal_terms ω hω hz hε hε8 A hA
  refine ⟨3 * max C0 1, fun x hx q hq hqA χ hχ t ht => ?_⟩
  have hx0 : C0 ≤ x := by
    have : max C0 1 ≤ 3 * max C0 1 := by have := le_max_right C0 1; linarith
    exact le_trans (le_trans (le_max_left _ _) this) hx
  obtain ⟨h1, h2, h3⟩ := hC0 x hx0 q hq hqA χ hχ t ht
  set S := (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t)
  have hsplit : ∑ m ∈ S, ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q)) =
      ∑ m ∈ S, ((lowerFactor ω ε x m * primeWeight m : ℝ) : ℂ) * χ (m : ZMod q) -
      ∑ m ∈ S, ((lowerFactor ω ε x m * lowerTwoTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q) -
      ∑ m ∈ S, ((lowerFactor ω ε x m * lowerFourTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold lowerShortWeight rawLower
    push_cast
    ring
  have hxone : 1 ≤ x := by
    have : 1 ≤ 3 * max C0 1 := by have := le_max_right C0 1; linarith
    linarith
  have hY : 0 ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
    have := Real.rpow_nonneg (by linarith : (0:ℝ) ≤ x) (11 / 20 + ε)
    have hl : 0 ≤ Real.log x := Real.log_nonneg hxone
    have := Real.rpow_nonneg hl (-A)
    positivity
  rw [hsplit]
  calc _ ≤ ‖∑ m ∈ S, ((lowerFactor ω ε x m * primeWeight m : ℝ) : ℂ) * χ (m : ZMod q) -
          ∑ m ∈ S, ((lowerFactor ω ε x m * lowerTwoTerms ε x m : ℝ) : ℂ) * χ (m : ZMod q)‖ +
        ‖∑ m ∈ S, ((lowerFactor ω ε x m * lowerFourTerms ε x m : ℝ) : ℂ) *
          χ (m : ZMod q)‖ := norm_sub_le _ _
    _ ≤ (‖∑ m ∈ S, ((lowerFactor ω ε x m * primeWeight m : ℝ) : ℂ) * χ (m : ZMod q)‖ +
          ‖∑ m ∈ S, ((lowerFactor ω ε x m * lowerTwoTerms ε x m : ℝ) : ℂ) *
            χ (m : ZMod q)‖) +
        ‖∑ m ∈ S, ((lowerFactor ω ε x m * lowerFourTerms ε x m : ℝ) : ℂ) *
          χ (m : ZMod q)‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ 3 * (C0 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by linarith
    _ ≤ 3 * max C0 1 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
      have : C0 * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ≤
          max C0 1 * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hY
      nlinarith

/-- LEAF, OPEN. P0069 Baker Harman Pintz 1997, Section 5, page 52, displays 5.18 to 5.23,
condition iv of Theorem 2, display 1.9 on page 3, for b0. Lemmas 33 to 35 on pages 48 to 50 give
5.1 and 5.2 for every retained term of 5.15, Lemma 29 on page 43 then gives 5.18 and 5.19,
and 5.20 to 5.23 replace `W(y, z)` by `z y v0 / log Y`. The U-1624 factor is constant to
within `L^(-K)` on blocks of length `Y L^(-K)`, which is how it passes through Lemma 29.
CONDITIONAL on the cited Theorem 4 and Lemma 9, the inputs of Lemmas 29 to 35. -/
theorem lower_exceptional_mean_square (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                    C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                      x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-! ### Assembly of condition iii -/

/-- P0069 Baker Harman Pintz 1997, page 3, display 1.8 for b0, with 5.17 on page 51: the principal and non-principal cases together. -/
theorem lower_short_distribution (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
      ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) -
            Thm2.delta χ * lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ≤
              C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C1, hC1⟩ := lower_principal_distribution ω hω hz hε hε8 A hA
  obtain ⟨C2, hC2⟩ := lower_nonprincipal_distribution ω hω hz hε hε8 A hA
  refine ⟨max (max C1 C2) 1, fun x hx q hq hqA χ t ht => ?_⟩
  have hx1 : C1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : C2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx0 : 0 < x := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hx)
  have hY : 0 ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
    have := Real.rpow_nonneg hx0.le (11 / 20 + ε)
    have hl : 0 ≤ Real.log x := Real.log_nonneg (le_trans (le_max_right _ _) hx)
    have := Real.rpow_nonneg hl (-A)
    positivity
  have hm1 : C1 ≤ max (max C1 C2) 1 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hm2 : C2 ≤ max (max C1 C2) 1 := le_trans (le_max_right _ _) (le_max_left _ _)
  by_cases hχ : χ = 1
  · subst hχ
    have h := hC1 x hx1 q hq hqA t ht
    have hd : Thm2.delta (1 : DirichletCharacter ℂ q) = 1 := by simp [Thm2.delta]
    rw [hd, one_mul]
    calc _ ≤ C1 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := h
      _ ≤ max (max C1 C2) 1 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right hm1 hY
  · have h := hC2 x hx2 q hq hqA χ hχ t ht
    have hd : Thm2.delta χ = 0 := by simp [Thm2.delta, hχ]
    rw [hd, zero_mul, zero_div]
    simp only [sub_zero]
    calc _ ≤ C2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := h
      _ ≤ max (max C1 C2) 1 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right hm2 hY

end LeanLab.BHP1997.LowerShortC165
