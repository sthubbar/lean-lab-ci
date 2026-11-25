/-
P0069 Baker Harman Pintz 1997, page 48, Lemma 33 and its proof, read from the page image
papers/P0069-original.pdf. Burst burst-20261122, session S130, unit upD_kept_52-p3 on the LEAF
kept52_lemma33_block of Prep1122KeptWellspacedSplit52.lean.

The proof of Lemma 33 treats the triangle R and the parallelograms P1 and P2 one at a time, each
by one application of Theorem 4 to a rearranged product, and the block [T, T + T2] is moved to a
block centred at 0 because Theorem 4 wants its well-spaced set inside [-T, T]. This file splits
the LEAF once along that proof:
1. s130_lemma33_centered_R, HARD, CONDITIONAL on Theorem 4: the case R on a centred block.
2. s130_lemma33_centered_P1, HARD, CONDITIONAL on Theorem 4: the case P1 on a centred block.
3. s130_lemma33_centered_P2, HARD, CONDITIONAL on Theorem 4: the case P2 on a centred block.
PROVED: s130_dirPoly_shift and s130_coeffBound_shift, copies of kept52_dirPoly_shift and
kept52_coeffBound_shift, which live in a file that imports this one; and
s130_lemma33_block_split, the exact statement of kept52_lemma33_block, from the three LEAFs by
the shift to the block centre and the case split of upperPairRegion.

New file, no new definition, no existing statement changed. AI wrote the Lean code.
Goldbach is open.
-/
import LeanLab.BHP1997.UpperShortC165Leaves

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open MeasureTheory

/-- P0069 page 48, the step "if t is in [T, T + T2]": the polynomial at 1/2 + i(t + T) is the
polynomial with coefficients twisted by n^(-iT) at 1/2 + it. Same proof as
kept52_dirPoly_shift. PROVED. -/
theorem s130_dirPoly_shift {q : ℕ} (a : ℕ → ℂ) (c₁ c₂ F : ℝ) (χ : DirichletCharacter ℂ q)
    (t T : ℝ) :
    Thm4.dirPoly a c₁ c₂ F χ (Thm4.half (t + T)) =
      Thm4.dirPoly (fun n => a n * (n : ℂ) ^ (-((T : ℂ) * I))) c₁ c₂ F χ (Thm4.half t) := by
  unfold Thm4.dirPoly Thm4.half
  refine Finset.sum_congr rfl fun n _ => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · have h1 : (1 / 2 + ((t + T : ℝ) : ℂ) * I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    have h2 : (1 / 2 + (t : ℂ) * I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    simp only [Nat.cast_zero]
    rw [Complex.zero_cpow h1, Complex.zero_cpow h2, div_zero, div_zero]
  · have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hsplit : (n : ℂ) ^ (1 / 2 + ((t + T : ℝ) : ℂ) * I) =
        (n : ℂ) ^ (1 / 2 + (t : ℂ) * I) * (n : ℂ) ^ ((T : ℂ) * I) := by
      rw [← Complex.cpow_add _ _ hn']; congr 1; push_cast; ring
    have hne1 : (n : ℂ) ^ (1 / 2 + (t : ℂ) * I) ≠ 0 :=
      fun h => hn' ((Complex.cpow_eq_zero_iff _ _).mp h).1
    have hne2 : (n : ℂ) ^ ((T : ℂ) * I) ≠ 0 :=
      fun h => hn' ((Complex.cpow_eq_zero_iff _ _).mp h).1
    simp only []
    rw [hsplit, Complex.cpow_neg]
    field_simp

/-- P0069 page 11, display 3.1 is kept by the twist by n^(-iT). Same proof as
kept52_coeffBound_shift. PROVED. -/
theorem s130_coeffBound_shift {a : ℕ → ℂ} {B : ℝ} (ha : Thm4.CoeffBound a B) (T : ℝ) :
    Thm4.CoeffBound (fun n => a n * (n : ℂ) ^ (-((T : ℂ) * I))) B := by
  intro n
  have h1 : ‖(n : ℂ) ^ (-((T : ℂ) * I))‖ ≤ 1 := by
    rcases eq_or_ne n 0 with rfl | hn
    · by_cases hT : T = 0
      · simp [hT]
      · have : -((T : ℂ) * I) ≠ 0 := by
          intro h; apply hT; have := congrArg Complex.im h; simpa using this
        simp [Complex.zero_cpow this]
    · rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp
  calc ‖a n * (n : ℂ) ^ (-((T : ℂ) * I))‖ = ‖a n‖ * ‖(n : ℂ) ^ (-((T : ℂ) * I))‖ := norm_mul _ _
    _ ≤ ‖a n‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ _ := by rw [mul_one]; exact ha n

/-- LEAF: P0069 page 48, proof of Lemma 33, case (beta1, beta2) in the triangle R: "we apply
Theorem 4 with N^2 L, LM, M, T2 in place of M, N, L, T. Thus (3.5) holds with X = Y^2",
alpha1 = (1 + beta2 - beta1)/2, alpha2 = (1 - beta2)/2, theta = 1/2 + theta2/4, (3.7) from
beta1 <= c2 and (3.6) from (5.14), for a well-spaced set in a block [-H, H] centred at 0 of
length 2H at most T2 = Y/qQ, the principal character. Paper's proof: |LMN|^2 = |N^2 L * LM * M|,
the product coefficients satisfy (3.1) with a larger B, M satisfies (3.2), and Theorem 4 at a
smaller eps with its own x equal to Y^2, see QUESTION 1 and 2 of the S52 notes.
CONDITIONAL on Theorem 4. HARD. -/
theorem s130_lemma33_centered_R (h4 : Thm4.Theorem4Paper) {ε : ℝ} (hε : 0 < ε)
    (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ B c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
      ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ H : ℝ, 0 ≤ H → 2 * H ≤ x ^ (11 / 20 + ε) / (q * sieveQ ε x) →
      ∀ S : Finset ℝ, (∀ t ∈ S, |t| ≤ H) →
        (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
      ∀ β₁ β₂ : ℝ, upperPairRegion ε β₁ β₂ → (2 * β₂ - (2 * (1 / 16 - 1 / 10 ^ 5)) + ε ≤ β₁ ∧ β₁ ≤ (36 * (2 * (1 / 16 - 1 / 10 ^ 5)) - 2) / 11 - ε) →
      ∀ eL eM eN : ℕ → ℂ, Thm4.CoeffBound eL B → Thm4.CoeffBound eM B →
        Thm4.CoeffBound eN B →
        (∀ A' : ℝ, 0 < A' → ∀ t ∈ S,
          ‖Thm4.dirPoly eM c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ≤
            K A' * ((x ^ (11 / 20 + ε)) ^ β₁) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
        (∀ A' : ℝ, 0 < A' → ∀ t ∈ S,
          ‖Thm4.dirPoly eN c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ≤
            K A' * ((x ^ (11 / 20 + ε)) ^ β₂) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
        ∑ t ∈ S, ‖Thm4.dirPoly eL c₁ c₂ ((x ^ (11 / 20 + ε)) ^ (1 - β₁ - β₂))
              (1 : DirichletCharacter ℂ q) (Thm4.half t) *
            Thm4.dirPoly eM c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁) (1 : DirichletCharacter ℂ q)
              (Thm4.half t) *
            Thm4.dirPoly eN c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ^ 2 ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: P0069 page 48, proof of Lemma 33, case (beta1, beta2) in the parallelogram P1:
"to get P1 we use M^2 N, L^2, N in place of M, N, L", alpha1 = (2 beta1 + beta2)/2,
alpha2 = 1 - beta1 - beta2, (3.6) becomes |4 beta1 + 3 beta2 - 2| <= theta2 - eps and (3.7)
becomes beta2 <= c2, for a well-spaced set in a block [-H, H] centred at 0 of length 2H at
most T2 = Y/qQ, the principal character. Paper's proof: |LMN|^2 = |M^2 N * L^2 * N|, N
satisfies (3.2), Theorem 4 with X = Y^2 at a smaller eps. CONDITIONAL on Theorem 4. HARD. -/
theorem s130_lemma33_centered_P1 (h4 : Thm4.Theorem4Paper) {ε : ℝ} (hε : 0 < ε)
    (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ B c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
      ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ H : ℝ, 0 ≤ H → 2 * H ≤ x ^ (11 / 20 + ε) / (q * sieveQ ε x) →
      ∀ S : Finset ℝ, (∀ t ∈ S, |t| ≤ H) →
        (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
      ∀ β₁ β₂ : ℝ, upperPairRegion ε β₁ β₂ → |4 * β₁ + 3 * β₂ - 2| ≤ (2 * (1 / 16 - 1 / 10 ^ 5)) - ε →
      ∀ eL eM eN : ℕ → ℂ, Thm4.CoeffBound eL B → Thm4.CoeffBound eM B →
        Thm4.CoeffBound eN B →
        (∀ A' : ℝ, 0 < A' → ∀ t ∈ S,
          ‖Thm4.dirPoly eM c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ≤
            K A' * ((x ^ (11 / 20 + ε)) ^ β₁) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
        (∀ A' : ℝ, 0 < A' → ∀ t ∈ S,
          ‖Thm4.dirPoly eN c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ≤
            K A' * ((x ^ (11 / 20 + ε)) ^ β₂) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
        ∑ t ∈ S, ‖Thm4.dirPoly eL c₁ c₂ ((x ^ (11 / 20 + ε)) ^ (1 - β₁ - β₂))
              (1 : DirichletCharacter ℂ q) (Thm4.half t) *
            Thm4.dirPoly eM c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁) (1 : DirichletCharacter ℂ q)
              (Thm4.half t) *
            Thm4.dirPoly eN c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ^ 2 ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: P0069 page 48, proof of Lemma 33, case (beta1, beta2) in the parallelogram P2:
"We get P2 by replacing beta1 by 1 - beta1 - beta2 in P1", that is Theorem 4 with L^2 N, M^2,
N in place of M, N, L, the roles of L and M exchanged, for a well-spaced set in a block [-H, H]
centred at 0 of length 2H at most T2 = Y/qQ, the principal character. N satisfies (3.2), and
Theorem 4 with X = Y^2 at a smaller eps. CONDITIONAL on Theorem 4. HARD. -/
theorem s130_lemma33_centered_P2 (h4 : Thm4.Theorem4Paper) {ε : ℝ} (hε : 0 < ε)
    (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ B c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
      ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ H : ℝ, 0 ≤ H → 2 * H ≤ x ^ (11 / 20 + ε) / (q * sieveQ ε x) →
      ∀ S : Finset ℝ, (∀ t ∈ S, |t| ≤ H) →
        (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
      ∀ β₁ β₂ : ℝ, upperPairRegion ε β₁ β₂ → |4 * β₁ + β₂ - 2| ≤ (2 * (1 / 16 - 1 / 10 ^ 5)) - ε →
      ∀ eL eM eN : ℕ → ℂ, Thm4.CoeffBound eL B → Thm4.CoeffBound eM B →
        Thm4.CoeffBound eN B →
        (∀ A' : ℝ, 0 < A' → ∀ t ∈ S,
          ‖Thm4.dirPoly eM c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ≤
            K A' * ((x ^ (11 / 20 + ε)) ^ β₁) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
        (∀ A' : ℝ, 0 < A' → ∀ t ∈ S,
          ‖Thm4.dirPoly eN c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ≤
            K A' * ((x ^ (11 / 20 + ε)) ^ β₂) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
        ∑ t ∈ S, ‖Thm4.dirPoly eL c₁ c₂ ((x ^ (11 / 20 + ε)) ^ (1 - β₁ - β₂))
              (1 : DirichletCharacter ℂ q) (Thm4.half t) *
            Thm4.dirPoly eM c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁) (1 : DirichletCharacter ℂ q)
              (Thm4.half t) *
            Thm4.dirPoly eN c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ^ 2 ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- P0069 page 48, Lemma 33 on one block [a, b] of length at most T2: the exact statement of
the LEAF kept52_lemma33_block. Proof: shift the block by its centre m = (a + b)/2 with
s130_dirPoly_shift, which keeps (3.1), (3.2) and the spacing, then the case split R, P1, P2 of
upperPairRegion and the three LEAFs above. PROVED from those LEAFs, so CONDITIONAL on them and on
Theorem 4. -/
theorem s130_lemma33_block_split (h4 : Thm4.Theorem4Paper) {ε : ℝ} (hε : 0 < ε)
    (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ B c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
      ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ a b : ℝ, a ≤ b → b - a ≤ x ^ (11 / 20 + ε) / (q * sieveQ ε x) →
      ∀ S : Finset ℝ, (∀ t ∈ S, a ≤ t ∧ t ≤ b) →
        (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
      ∀ β₁ β₂ : ℝ, upperPairRegion ε β₁ β₂ →
      ∀ eL eM eN : ℕ → ℂ, Thm4.CoeffBound eL B → Thm4.CoeffBound eM B →
        Thm4.CoeffBound eN B →
        (∀ A' : ℝ, 0 < A' → ∀ t ∈ S,
          ‖Thm4.dirPoly eM c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ≤
            K A' * ((x ^ (11 / 20 + ε)) ^ β₁) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
        (∀ A' : ℝ, 0 < A' → ∀ t ∈ S,
          ‖Thm4.dirPoly eN c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ≤
            K A' * ((x ^ (11 / 20 + ε)) ^ β₂) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
        ∑ t ∈ S, ‖Thm4.dirPoly eL c₁ c₂ ((x ^ (11 / 20 + ε)) ^ (1 - β₁ - β₂))
              (1 : DirichletCharacter ℂ q) (Thm4.half t) *
            Thm4.dirPoly eM c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁) (1 : DirichletCharacter ℂ q)
              (Thm4.half t) *
            Thm4.dirPoly eN c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ^ 2 ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro B c₁ c₂ hc₁ hc₁₂ K A hA
  obtain ⟨CR, hR⟩ := s130_lemma33_centered_R h4 hε hε8 B c₁ c₂ hc₁ hc₁₂ K A hA
  obtain ⟨C1, hP1⟩ := s130_lemma33_centered_P1 h4 hε hε8 B c₁ c₂ hc₁ hc₁₂ K A hA
  obtain ⟨C2, hP2⟩ := s130_lemma33_centered_P2 h4 hε hε8 B c₁ c₂ hc₁ hc₁₂ K A hA
  refine ⟨max (max CR (max C1 C2)) 2, ?_⟩
  intro x hx q hq1 hqQ a b hab hba S hS hsp β₁ β₂ hreg eL eM eN hL hM hN h32M h32N
  have hCR : CR ≤ max (max CR (max C1 C2)) 2 :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hC1 : C1 ≤ max (max CR (max C1 C2)) 2 :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have hC2 : C2 ≤ max (max CR (max C1 C2)) 2 :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
  have hx2' : (2 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hxR : CR ≤ x := le_trans hCR hx
  have hx1 : C1 ≤ x := le_trans hC1 hx
  have hx2 : C2 ≤ x := le_trans hC2 hx
  have hY0 : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (by linarith) _
  have hlog0 : 0 ≤ Real.log x ^ (-A) :=
    Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  have hmono : ∀ C' : ℝ, C' ≤ max (max CR (max C1 C2)) 2 →
      C' * x ^ (11 / 20 + ε) * Real.log x ^ (-A) ≤
        max (max CR (max C1 C2)) 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    fun C' h => mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hY0) hlog0
  set m : ℝ := (a + b) / 2 with hm
  have key : ∀ (e : ℕ → ℂ) (F t : ℝ),
      Thm4.dirPoly (fun n => e n * (n : ℂ) ^ (-((m : ℂ) * I))) c₁ c₂ F
          (1 : DirichletCharacter ℂ q) (Thm4.half (t - m)) =
        Thm4.dirPoly e c₁ c₂ F (1 : DirichletCharacter ℂ q) (Thm4.half t) := by
    intro e F t
    have h := s130_dirPoly_shift e c₁ c₂ F (1 : DirichletCharacter ℂ q) (t - m) m
    rw [sub_add_cancel] at h
    exact h.symm
  set S' : Finset ℝ := S.image (fun t => t - m) with hS'def
  have hsum : ∀ g : ℝ → ℝ, ∑ t ∈ S', g t = ∑ t ∈ S, g (t - m) := by
    intro g
    rw [hS'def, Finset.sum_image]
    intro u _ v _ h
    simpa using h
  have hH0 : 0 ≤ (b - a) / 2 := by linarith
  have hH : 2 * ((b - a) / 2) ≤ x ^ (11 / 20 + ε) / (q * sieveQ ε x) := by
    have : 2 * ((b - a) / 2) = b - a := by ring
    rw [this]; exact hba
  have hS' : ∀ t ∈ S', |t| ≤ (b - a) / 2 := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨h1, h2⟩ := hS s hs
    rw [abs_le]; constructor <;> linarith
  have hsp' : ∀ t ∈ S', ∀ t' ∈ S', t ≠ t' → 1 ≤ |t - t'| := by
    intro t ht t' ht' hne
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp ht'
    have hne' : s ≠ s' := fun h => hne (by rw [h])
    have := hsp s hs s' hs' hne'
    rwa [sub_sub_sub_cancel_right]
  have h32M' : ∀ A' : ℝ, 0 < A' → ∀ t ∈ S',
      ‖Thm4.dirPoly (fun n => eM n * (n : ℂ) ^ (-((m : ℂ) * I))) c₁ c₂
          ((x ^ (11 / 20 + ε)) ^ β₁) (1 : DirichletCharacter ℂ q) (Thm4.half t)‖ ≤
        K A' * ((x ^ (11 / 20 + ε)) ^ β₁) ^ (1 / 2 : ℝ) * Real.log x ^ (-A') := by
    intro A' hA' t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    rw [key]; exact h32M A' hA' s hs
  have h32N' : ∀ A' : ℝ, 0 < A' → ∀ t ∈ S',
      ‖Thm4.dirPoly (fun n => eN n * (n : ℂ) ^ (-((m : ℂ) * I))) c₁ c₂
          ((x ^ (11 / 20 + ε)) ^ β₂) (1 : DirichletCharacter ℂ q) (Thm4.half t)‖ ≤
        K A' * ((x ^ (11 / 20 + ε)) ^ β₂) ^ (1 / 2 : ℝ) * Real.log x ^ (-A') := by
    intro A' hA' t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    rw [key]; exact h32N A' hA' s hs
  have hL' := s130_coeffBound_shift hL m
  have hM' := s130_coeffBound_shift hM m
  have hN' := s130_coeffBound_shift hN m
  have hmove :
      ∑ t ∈ S, ‖Thm4.dirPoly eL c₁ c₂ ((x ^ (11 / 20 + ε)) ^ (1 - β₁ - β₂))
              (1 : DirichletCharacter ℂ q) (Thm4.half t) *
            Thm4.dirPoly eM c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₁) (1 : DirichletCharacter ℂ q)
              (Thm4.half t) *
            Thm4.dirPoly eN c₁ c₂ ((x ^ (11 / 20 + ε)) ^ β₂) (1 : DirichletCharacter ℂ q)
              (Thm4.half t)‖ ^ 2 =
        ∑ t ∈ S', ‖Thm4.dirPoly (fun n => eL n * (n : ℂ) ^ (-((m : ℂ) * I))) c₁ c₂
              ((x ^ (11 / 20 + ε)) ^ (1 - β₁ - β₂))
              (1 : DirichletCharacter ℂ q) (Thm4.half t) *
            Thm4.dirPoly (fun n => eM n * (n : ℂ) ^ (-((m : ℂ) * I))) c₁ c₂
              ((x ^ (11 / 20 + ε)) ^ β₁) (1 : DirichletCharacter ℂ q) (Thm4.half t) *
            Thm4.dirPoly (fun n => eN n * (n : ℂ) ^ (-((m : ℂ) * I))) c₁ c₂
              ((x ^ (11 / 20 + ε)) ^ β₂) (1 : DirichletCharacter ℂ q) (Thm4.half t)‖ ^ 2 := by
    rw [hsum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [key, key, key]
  rw [hmove]
  rcases hreg.2.2.2.2 with hc | hc | hc
  · refine le_trans ?_ (hmono _ hCR)
    exact hR x hxR q hq1 hqQ ((b - a) / 2) hH0 hH S' hS' hsp' β₁ β₂ hreg hc _ _ _
        hL' hM' hN' h32M' h32N'
  · refine le_trans ?_ (hmono _ hC1)
    exact hP1 x hx1 q hq1 hqQ ((b - a) / 2) hH0 hH S' hS' hsp' β₁ β₂ hreg hc _ _ _
        hL' hM' hN' h32M' h32N'
  · refine le_trans ?_ (hmono _ hC2)
    exact hP2 x hx2 q hq1 hqQ ((b - a) / 2) hH0 hH S' hS' hsp' β₁ β₂ hreg hc _ _ _
        hL' hM' hN' h32M' h32N'

end LeanLab.BHP1997.DecompC165d
