/-
The circle method skeleton of the exceptional set bound, P0015 Montgomery-Vaughan 1975 and
every later exceptional set paper, on ZMod M, unconditional. Unit U-0993, route R-0001 salvage.
E(x) ≤ #{even n ≤ x : major arc part ≤ T} + M ∑_{minor} |S|⁴ / T².
AI wrote this Lean code. Binary Goldbach is open; this is the frame the papers fill in.
-/
import LeanLab.Routes.R0001Markov
import LeanLab.ExceptionalSet.Statements

open ZMod Finset

namespace LeanLab.ExceptionalSet.MV
open LeanLab.Routes.R0001

variable {M : ℕ} [NeZero M]

attribute [local instance] Classical.propDecidable

/-- The circle method convolution identity on `ZMod M`. -/
theorem sum_dft_sq (Φ : ZMod M → ℂ) (n : ZMod M) :
    ∑ k, 𝓕 Φ k ^ 2 * (stdAddChar (n * k) : ℂ) = (M : ℂ) * ∑ j, Φ j * Φ (n - j) := by
  classical
  simp only [dft_apply, smul_eq_mul, sq, Finset.sum_mul, Finset.mul_sum]
  -- ∑ k ∑ i ∑ j e(-ik) Φ i e(-jk) Φ j e(nk)
  have hk : ∀ i j : ZMod M,
      ∑ k : ZMod M, (stdAddChar (-(i * k)) : ℂ) * Φ i * ((stdAddChar (-(j * k)) : ℂ) * Φ j)
        * (stdAddChar (n * k) : ℂ) = Φ i * Φ j * (if n - i - j = 0 then (M : ℂ) else 0) := by
    intro i j
    rw [← sum_stdAddChar_mul (n - i - j), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : (stdAddChar (k * (n - i - j)) : ℂ)
        = stdAddChar (-(i * k)) * stdAddChar (-(j * k)) * stdAddChar (n * k) := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]; ring_nf
    rw [this]; ring
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm]
  simp only [hk]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : ∀ j : ZMod M, (n - i - j = 0 ↔ j = n - i) := fun j =>
    ⟨fun h => by linear_combination -h, fun h => by rw [h]; ring⟩
  simp only [this, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- Support hypothesis: `Φ` lives on primes up to `x`. -/
def PrimeSupported (Φ : ZMod M → ℂ) (x : ℕ) : Prop :=
  ∀ j : ZMod M, Φ j ≠ 0 → (ZMod.val j).Prime ∧ ZMod.val j ≤ x

/-- A nonzero convolution at `n`, with `2x < M` and `n < M`, makes `n` a Goldbach sum. -/
theorem goldbach_of_conv_ne_zero {Φ : ZMod M → ℂ} {x : ℕ} (hΦ : PrimeSupported Φ x)
    (hM : 2 * x < M) {n : ℕ} (hn : n < M)
    (h : ∑ j, Φ j * Φ ((n : ZMod M) - j) ≠ 0) : IsGoldbachSum n := by
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have h1 : Φ j ≠ 0 := left_ne_zero_of_mul hj
  have h2 : Φ ((n : ZMod M) - j) ≠ 0 := right_ne_zero_of_mul hj
  obtain ⟨hp, hpx⟩ := hΦ j h1
  obtain ⟨hq, hqx⟩ := hΦ _ h2
  refine ⟨ZMod.val j, ZMod.val ((n : ZMod M) - j), hp, hq, ?_⟩
  have hmod : ((ZMod.val j + ZMod.val ((n : ZMod M) - j) : ℕ) : ZMod M) = (n : ZMod M) := by
    push_cast; simp [ZMod.natCast_val, ZMod.cast_id']
  rw [ZMod.natCast_eq_natCast_iff'] at hmod
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hn] at hmod
  exact hmod

/-- The major arc part, unnormalized, over the complement of the minor arcs `m`. -/
noncomputable def majorPart (Φ : ZMod M → ℂ) (m : Finset (ZMod M)) (n : ZMod M) : ℂ :=
  ∑ k ∈ mᶜ, 𝓕 Φ k ^ 2 * (stdAddChar (n * k) : ℂ)

/-- **The exceptional set skeleton.** For `Φ` on the primes up to `x`, `M > 2x`, any minor arc
set `m` and any `T > 0`: `E(x)` is at most the number of even `n` in `[4, x]` whose major arc
part has modulus at most `T`, plus `M ∑_{k∈m} |S(k)|⁴ / T²`. Unconditional. The papers supply
a lower bound for the major arc part, which makes the first count small, and an upper bound
for the minor arc L4 mass. -/
theorem E_le_skeleton {Φ : ZMod M → ℂ} {x : ℕ} (hΦ : PrimeSupported Φ x) (hM : 2 * x < M)
    (m : Finset (ZMod M)) {T : ℝ} (hT : 0 < T) :
    (E x : ℝ) ≤ (((Finset.Icc 4 x).filter
        (fun n : ℕ => Even n ∧ ‖majorPart Φ m (n : ZMod M)‖ ≤ T)).card : ℝ)
      + (M : ℝ) * (∑ k ∈ m, ‖𝓕 Φ k‖ ^ 4) / T ^ 2 := by
  classical
  set A := (Finset.Icc 4 x).filter (fun n : ℕ => Even n ∧ ‖majorPart Φ m (n : ZMod M)‖ ≤ T)
  set B := (Finset.Icc 4 x).filter (fun n : ℕ => T ≤ ‖minorPart Φ m (n : ZMod M)‖)
  have hsub : (Finset.Icc 4 x).filter (fun n => Even n ∧ ¬ IsGoldbachSum n) ⊆ A ∪ B := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨h4, hx⟩, he, hng⟩ := hn
    have hnM : n < M := by omega
    have hzero : majorPart Φ m (n : ZMod M) + minorPart Φ m (n : ZMod M) = 0 := by
      unfold majorPart minorPart
      rw [add_comm, Finset.sum_add_sum_compl, sum_dft_sq]
      by_contra hne
      exact hng (goldbach_of_conv_ne_zero hΦ hM hnM (right_ne_zero_of_mul hne))
    have heq : ‖majorPart Φ m (n : ZMod M)‖ = ‖minorPart Φ m (n : ZMod M)‖ := by
      rw [eq_neg_of_add_eq_zero_left hzero, norm_neg]
    rcases le_or_gt (‖majorPart Φ m (n : ZMod M)‖) T with h | h
    · exact Finset.mem_union_left _ (by simp [A, h4, hx, he, h])
    · exact Finset.mem_union_right _ (by simp [B, h4, hx, ← heq, h.le])
  have hB : (B.card : ℝ) * T ^ 2 ≤ (M : ℝ) * ∑ k ∈ m, ‖𝓕 Φ k‖ ^ 4 := by
    refine le_trans ?_ (card_large_minor_le Φ m T hT.le)
    gcongr
    refine Finset.card_le_card_of_injOn (fun n => (n : ZMod M)) ?_ ?_
    · intro n hn
      simp only [B, Finset.coe_filter, Set.mem_ofPred_eq] at hn
      simp [hn.2]
    · intro a ha b hb hab
      simp only [B, Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at ha hb
      have := (ZMod.natCast_eq_natCast_iff' a b M).1 hab
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  have hB' : (B.card : ℝ) ≤ (M : ℝ) * (∑ k ∈ m, ‖𝓕 Φ k‖ ^ 4) / T ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; exact hB
  have hE : (E x : ℝ) ≤ ((A ∪ B).card : ℝ) := by
    unfold E; exact_mod_cast Finset.card_le_card hsub
  have hU : ((A ∪ B).card : ℝ) ≤ A.card + B.card := by
    exact_mod_cast Finset.card_union_le A B
  linarith

/-- **The skeleton on a window** `[a, x]`, the dyadic form the papers use. For `Φ` on the primes up to `x`, `M > 2x`, any minor arc
set `m` and any `T > 0`: `E(x)` is at most the number of even `n` in `[4, x]` whose major arc
part has modulus at most `T`, plus `M ∑_{k∈m} |S(k)|⁴ / T²`. Unconditional. The papers supply
a lower bound for the major arc part, which makes the first count small, and an upper bound
for the minor arc L4 mass. -/
theorem bad_le_skeleton {Φ : ZMod M → ℂ} {x : ℕ} (hΦ : PrimeSupported Φ x) (hM : 2 * x < M)
    (m : Finset (ZMod M)) {T : ℝ} (hT : 0 < T) (a : ℕ) :
    ((((Finset.Icc a x).filter (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℕ) : ℝ) ≤ (((Finset.Icc a x).filter
        (fun n : ℕ => Even n ∧ ‖majorPart Φ m (n : ZMod M)‖ ≤ T)).card : ℝ)
      + (M : ℝ) * (∑ k ∈ m, ‖𝓕 Φ k‖ ^ 4) / T ^ 2 := by
  classical
  set A := (Finset.Icc a x).filter (fun n : ℕ => Even n ∧ ‖majorPart Φ m (n : ZMod M)‖ ≤ T)
  set B := (Finset.Icc a x).filter (fun n : ℕ => T ≤ ‖minorPart Φ m (n : ZMod M)‖)
  have hsub : (Finset.Icc a x).filter (fun n => Even n ∧ ¬ IsGoldbachSum n) ⊆ A ∪ B := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨h4, hx⟩, he, hng⟩ := hn
    have hnM : n < M := by omega
    have hzero : majorPart Φ m (n : ZMod M) + minorPart Φ m (n : ZMod M) = 0 := by
      unfold majorPart minorPart
      rw [add_comm, Finset.sum_add_sum_compl, sum_dft_sq]
      by_contra hne
      exact hng (goldbach_of_conv_ne_zero hΦ hM hnM (right_ne_zero_of_mul hne))
    have heq : ‖majorPart Φ m (n : ZMod M)‖ = ‖minorPart Φ m (n : ZMod M)‖ := by
      rw [eq_neg_of_add_eq_zero_left hzero, norm_neg]
    rcases le_or_gt (‖majorPart Φ m (n : ZMod M)‖) T with h | h
    · exact Finset.mem_union_left _ (by simp [A, h4, hx, he, h])
    · exact Finset.mem_union_right _ (by simp [B, h4, hx, ← heq, h.le])
  have hB : (B.card : ℝ) * T ^ 2 ≤ (M : ℝ) * ∑ k ∈ m, ‖𝓕 Φ k‖ ^ 4 := by
    refine le_trans ?_ (card_large_minor_le Φ m T hT.le)
    gcongr
    refine Finset.card_le_card_of_injOn (fun n => (n : ZMod M)) ?_ ?_
    · intro n hn
      simp only [B, Finset.coe_filter, Set.mem_ofPred_eq] at hn
      simp [hn.2]
    · intro a ha b hb hab
      simp only [B, Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at ha hb
      have := (ZMod.natCast_eq_natCast_iff' a b M).1 hab
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  have hB' : (B.card : ℝ) ≤ (M : ℝ) * (∑ k ∈ m, ‖𝓕 Φ k‖ ^ 4) / T ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; exact hB
  have hE : ((((Finset.Icc a x).filter (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℕ) : ℝ)
      ≤ ((A ∪ B).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hU : ((A ∪ B).card : ℝ) ≤ A.card + B.card := by
    exact_mod_cast Finset.card_union_le A B
  linarith

/-- Splitting `E` at `y`: `E x ≤ E y + #{bad n in [y+1, x]}`. -/
theorem E_le_split (y x : ℕ) :
    E x ≤ E y + ((Finset.Icc (y + 1) x).filter (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card := by
  classical
  unfold E
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union] at hn ⊢
  by_cases h : n ≤ y
  · exact Or.inl ⟨⟨hn.1.1, h⟩, hn.2⟩
  · exact Or.inr ⟨⟨by omega, hn.1.2⟩, hn.2⟩

/-- Vacuity test: the support hypothesis holds for the log-weighted prime indicator itself,
the `Φ` every paper uses, so `E_le_skeleton` is not vacuous. -/
theorem primeSupported_logPrimes (x : ℕ) :
    PrimeSupported (M := M)
      (fun j => if (ZMod.val j).Prime ∧ ZMod.val j ≤ x then (Real.log (ZMod.val j) : ℂ) else 0) x := by
  intro j hj
  by_contra h
  exact hj (by simp [h])

end LeanLab.ExceptionalSet.MV
