/-
Split of `LeanLab.BHP1997.LowerShortC165.lower_exceptional_mean_square`, the short-weight
development of section 5, as one NEW file. The sealed statement is untouched.

The target asks for a family `E A x q` of characters, a count for that family, and a squared
short-interval mean square taken over the characters that are left. Two independent estimates
make it up: the size of the exceptional family, and the mean square on the kept characters. The
count is free here, since the empty family satisfies it with constant `0`; that is recorded with
a full proof in `exceptional_count_empty` below, so all the work sits in the mean square.

The mean square is cut into the three window-length regimes of the section: a very short window,
a window of medium length, and a long window. Each leaf restricts the sealed `z` quantifier to
one regime and keeps its own family and its own count, so the assembly takes the union of the
three families, pays one cardinality step for the union and one monotonicity step for the
smaller sum, and then picks the regime that contains `z`.

Every leaf is open; the assembly is complete and uses no `sorry`.
-/
import LeanLab.BHP1997.LowerShortC165

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d
open scoped BigOperators
set_option maxHeartbeats 400000

/-! ### Small helper lemmas, fully proved -/

/-- A squared norm is nonnegative, so its interval integral is nonnegative. -/
private theorem integral_norm_sq_nonneg (f : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ ∫ y in a..b, ‖f y‖ ^ 2 :=
  intervalIntegral.integral_nonneg hab (fun u _ => by positivity)

/-- Dropping more characters leaves fewer terms in the sum, and every term here is
nonnegative. -/
private theorem sum_compl_le_of_subset {q : ℕ} {f : DirichletCharacter ℂ q → ℝ}
    {E E' : Finset (DirichletCharacter ℂ q)} (h : E' ⊆ E) (hf : ∀ χ, 0 ≤ f χ) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E, f χ ≤
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E', f χ := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro χ hχ
    simp only [Finset.mem_sdiff] at hχ ⊢
    exact ⟨hχ.1, fun hh => hχ.2 (h hh)⟩
  · intro χ _ _
    exact hf χ

/-- The cardinality of a union of three sets against the sum of the three cardinalities. -/
private theorem card_union_three_le {α : Type*} [DecidableEq α] (s t u : Finset α) :
    ((s ∪ t ∪ u).card : ℝ) ≤ (s.card : ℝ) + (t.card : ℝ) + (u.card : ℝ) := by
  have h1 : (s ∪ t ∪ u).card ≤ (s ∪ t).card + u.card := Finset.card_union_le _ _
  have h2 : (s ∪ t).card ≤ s.card + t.card := Finset.card_union_le _ _
  have h3 : (s ∪ t ∪ u).card ≤ s.card + t.card + u.card := by omega
  exact_mod_cast h3

/-- Weakening the constant in a product of four nonnegative factors. -/
private theorem const_mul_le {a b c d e : ℝ} (h : a ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) : a * c * d * e ≤ b * c * d * e := by
  have hq : (0:ℝ) ≤ c * d * e := mul_nonneg (mul_nonneg hc hd) he
  have h1 : a * (c * d * e) ≤ b * (c * d * e) := mul_le_mul_of_nonneg_right h hq
  calc a * c * d * e = a * (c * d * e) := by ring
    _ ≤ b * (c * d * e) := h1
    _ = b * c * d * e := by ring

/-- The exceptional family may be taken empty: the count then holds with constant `0`. This is
the whole content of the cardinality half of the sealed statement. -/
private theorem exceptional_count_empty {ε : ℝ} :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) :=
  ⟨fun _ _ _ => ∅, fun A hA => ⟨0, fun x hx q hq hqQ => by simp⟩⟩

/-! ### The three window regimes, open leaves -/

/-- LEAF: the mean square on the shortest windows, `z` at most
`q * sieveQ ε x / x ^ (11 / 20 + ε)`, where the window `[y, y + y z]` holds at most about
`q * sieveQ ε x` integers. This is the regime where the second moment in `y` is applied
directly to the short-interval sum after the main term
`lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε))` has been separated from the weight: the variation
of the main term is what the window length bounds, and the rest is controlled by the
exponential-sum input `h4` at exponents read from the two Dirichlet polynomials of lengths about
`y z` and `y / (y z)`. The family `E` and its count are carried here because that input is only
stated for characters outside a small family. -/
theorem leaf_mean_square_low_z (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ (q * sieveQ ε x : ℝ) / x ^ (11 / 20 + ε) →
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                    C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                      x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: the mean square on windows of medium length, with `z` between
`q * sieveQ ε x / x ^ (11 / 20 + ε)` and `2 * q * sieveQ ε x / x ^ (11 / 20 + ε)`, so that the
window length `y z` is comparable with `q * sieveQ ε x` for every `y` in the range. This is the
central regime: the square of the short-interval sum is expanded over pairs of coefficients with
equal difference, and the fourth-moment input `h9` turns the whole `y`-integral of the squared
sum into `((q : ℝ) * sieveQ ε x) ^ 2` times the length of the range, the saving
`Real.log x ^ (-A)` coming from the fourth power. Characters whose contribution exceeds the
average are collected into `E`, which is where its count comes from. -/
theorem leaf_mean_square_mid_z (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / x ^ (11 / 20 + ε) ≤ z →
          z ≤ 2 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                    C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                      x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: the mean square on the longest windows, with `z` between
`2 * q * sieveQ ε x / x ^ (11 / 20 + ε)` and `6 * q * sieveQ ε x / x ^ (11 / 20 + ε)`, where the
window is several times longer than `q * sieveQ ε x`. Here the short-interval sum is replaced by
the difference of two sums over the whole range, by the centring identity for the weight and its
mean value `lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε))`; what results is estimated by the same
fourth-moment input `h9` at a well-spaced set of points, and the characters on which it fails go
into `E`. The factor `((q : ℝ) * sieveQ ε x) ^ 2` is what remains after the window length has
cancelled against the length of the range. -/
theorem leaf_mean_square_high_z (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, 2 * q * sieveQ ε x / x ^ (11 / 20 + ε) ≤ z →
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

/-! ### Assembly -/

theorem lower_exceptional_mean_square_split (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
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
  obtain ⟨E1, hE1⟩ := leaf_mean_square_low_z h4 h9 ω hω hz hε hε8
  obtain ⟨E2, hE2⟩ := leaf_mean_square_mid_z h4 h9 ω hω hz hε hε8
  obtain ⟨E3, hE3⟩ := leaf_mean_square_high_z h4 h9 ω hω hz hε hε8
  refine ⟨fun A x q => (E1 A x q ∪ E2 A x q ∪ E3 A x q), fun A hA => ?_⟩
  obtain ⟨C1, hC1⟩ := hE1 A hA
  obtain ⟨C2, hC2⟩ := hE2 A hA
  obtain ⟨C3, hC3⟩ := hE3 A hA
  refine ⟨3 * max (max C1 (max C2 C3)) 0 + 2, fun x hx q hq hqQ => ⟨?_, ?_⟩⟩
  · obtain ⟨e1, -⟩ := hC1 x (by linarith [le_max_left (max C1 (max C2 C3)) 0, le_max_right (max C1 (max C2 C3)) 0, le_max_left C1 (max C2 C3)]) q hq hqQ
    obtain ⟨e2, -⟩ := hC2 x (by linarith [le_max_left (max C1 (max C2 C3)) 0, le_max_right (max C1 (max C2 C3)) 0, le_max_right C1 (max C2 C3), le_max_left C2 C3]) q hq hqQ
    obtain ⟨e3, -⟩ := hC3 x (by linarith [le_max_left (max C1 (max C2 C3)) 0, le_max_right (max C1 (max C2 C3)) 0, le_max_right C1 (max C2 C3), le_max_right C2 C3]) q hq hqQ
    have hx1 : (1:ℝ) ≤ x := by linarith [le_max_right (max C1 (max C2 C3)) 0]
    have hq0 : (0:ℝ) ≤ (q:ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
    have hl0 : (0:ℝ) ≤ Real.log x ^ (-2 * A) := Real.rpow_nonneg (Real.log_nonneg hx1) _
    have hqR : (0:ℝ) ≤ ((q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A)) := mul_nonneg hq0 hl0
    calc ((((E1 A x q ∪ E2 A x q ∪ E3 A x q)).card : ℝ))
        ≤ ((E1 A x q).card : ℝ) + ((E2 A x q).card : ℝ) + ((E3 A x q).card : ℝ) := card_union_three_le _ _ _
      _ ≤ C1 * ((q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A)) + C2 * ((q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A)) + C3 * ((q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A)) := by linarith
      _ = (C1 + C2 + C3) * ((q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A)) := by ring
      _ ≤ (3 * max (max C1 (max C2 C3)) 0 + 2) * ((q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A)) := by
          apply mul_le_mul_of_nonneg_right _ hqR
          linarith [le_max_left (max C1 (max C2 C3)) 0, le_max_right (max C1 (max C2 C3)) 0, le_max_right C1 (max C2 C3), le_max_left C1 (max C2 C3), le_max_left C2 C3, le_max_right C2 C3]
      _ = (3 * max (max C1 (max C2 C3)) 0 + 2) * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) := by ring
  · intro z hzlo hzhi
    have hx1 : (1:ℝ) ≤ x := by linarith [le_max_right (max C1 (max C2 C3)) 0]
    have hx0 : (0:ℝ) ≤ x := by linarith
    have hY : (0:ℝ) ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg hx0 _
    have hab : x ^ (11 / 20 + ε) / 2 ≤ 3 * x ^ (11 / 20 + ε) := by linarith
    have hq2 : (0:ℝ) ≤ ((q : ℝ) * sieveQ ε x) ^ 2 := sq_nonneg _
    have hL : (0:ℝ) ≤ Real.log x ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hx1) _
    have hR : (0:ℝ) ≤ ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := mul_nonneg (mul_nonneg hq2 hY) hL
    have hint : ∀ χ : DirichletCharacter ℂ q, 0 ≤ ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)), ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) - Thm2.delta χ * lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 :=
      fun χ => integral_norm_sq_nonneg (fun y => ∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) - Thm2.delta χ * lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))) hab
    by_cases hA : z ≤ (q * sieveQ ε x : ℝ) / x ^ (11 / 20 + ε)
    · calc ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ (E1 A x q ∪ E2 A x q ∪ E3 A x q),
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)), ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) - Thm2.delta χ * lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2
          ≤ ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E1 A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)), ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) - Thm2.delta χ * lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 := sum_compl_le_of_subset (E' := E1 A x q) (fun χ hχ => by simp only [Finset.mem_union]; tauto) hint
        _ ≤ C1 * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := (hC1 x (by linarith [le_max_left (max C1 (max C2 C3)) 0, le_max_right (max C1 (max C2 C3)) 0, le_max_left C1 (max C2 C3)]) q hq hqQ).2 z hzlo hA
        _ ≤ (3 * max (max C1 (max C2 C3)) 0 + 2) * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
            have hstep : C1 ≤ (3 * max (max C1 (max C2 C3)) 0 + 2) := by linarith [le_max_left (max C1 (max C2 C3)) 0, le_max_right (max C1 (max C2 C3)) 0, le_max_right C1 (max C2 C3), le_max_left C1 (max C2 C3), le_max_left C2 C3, le_max_right C2 C3]
            exact const_mul_le hstep hq2 hY hL
    · push_neg at hA
      by_cases hB : z ≤ 2 * q * sieveQ ε x / x ^ (11 / 20 + ε)
      · calc ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ (E1 A x q ∪ E2 A x q ∪ E3 A x q),
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)), ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) - Thm2.delta χ * lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2
            ≤ ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E2 A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)), ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) - Thm2.delta χ * lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 := sum_compl_le_of_subset (E' := E2 A x q) (fun χ hχ => by simp only [Finset.mem_union]; tauto) hint
          _ ≤ C2 * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := (hC2 x (by linarith [le_max_left (max C1 (max C2 C3)) 0, le_max_right (max C1 (max C2 C3)) 0, le_max_right C1 (max C2 C3), le_max_left C2 C3]) q hq hqQ).2 z hA.le hB
          _ ≤ (3 * max (max C1 (max C2 C3)) 0 + 2) * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
              have hstep : C2 ≤ (3 * max (max C1 (max C2 C3)) 0 + 2) := by linarith [le_max_left (max C1 (max C2 C3)) 0, le_max_right (max C1 (max C2 C3)) 0, le_max_right C1 (max C2 C3), le_max_left C1 (max C2 C3), le_max_left C2 C3, le_max_right C2 C3]
              exact const_mul_le hstep hq2 hY hL
      · push_neg at hB
        calc ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ (E1 A x q ∪ E2 A x q ∪ E3 A x q),
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)), ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) - Thm2.delta χ * lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2
              ≤ ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E3 A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)), ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), ((lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) - Thm2.delta χ * lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 := sum_compl_le_of_subset (E' := E3 A x q) (fun χ hχ => by simp only [Finset.mem_union]; tauto) hint
            _ ≤ C3 * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := (hC3 x (by linarith [le_max_left (max C1 (max C2 C3)) 0, le_max_right (max C1 (max C2 C3)) 0, le_max_right C1 (max C2 C3), le_max_right C2 C3]) q hq hqQ).2 z hB.le hzhi
            _ ≤ (3 * max (max C1 (max C2 C3)) 0 + 2) * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
                have hstep : C3 ≤ (3 * max (max C1 (max C2 C3)) 0 + 2) := by linarith [le_max_left (max C1 (max C2 C3)) 0, le_max_right (max C1 (max C2 C3)) 0, le_max_right C1 (max C2 C3), le_max_left C1 (max C2 C3), le_max_left C2 C3, le_max_right C2 C3]
                exact const_mul_le hstep hq2 hY hL

end LeanLab.BHP1997.LowerShortC165
