/-
P0068 Zhan 1991, Lemma 6 of page 262, cited from Pan and Pan [9], split into one cited LEAF.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Split of `Lemma6` of SPLIT_theorem2_1122.lean, the mean value theorem for Dirichlet polynomials
with characters:
1. `char_orth_sq`, PROVED: orthogonality of the characters mod `q`,
   `Σ_χ |Σ_r χ(r) B_r|² = φ(q) Σ_{r unit} |B_r|²`, so that
   `Σ_χ |Σ_n a_n χ(n)|² = φ(q) Σ_{r unit} |Σ_{n ≡ r} a_n|²`.
2. `mv_one_class_leaf`, LEAF HARD: the Montgomery Vaughan mean value theorem, 1974, applied to the
   integers of one residue class mod `q`, whose log spacings near `n` are at least about `q/n`.
3. `lemma6_of_mv`, PROVED: `Lemma6` from the LEAF, with `φ(q) ≤ q`.
-/
import LeanLab.Zhan1991.SPLIT_theorem2_1122

namespace LeanLab.Zhan1991
open Finset

noncomputable section

/-- The Montgomery Vaughan mean value theorem, Montgomery and Vaughan 1974, Hilbert's inequality,
for distinct positive integers of one residue class `r mod q`, as used in the proof of Lemma 6 of
page 262 cited from [9]: `∫_U^{U+T} |Σ_{n∈S} b_n n^{-it}|² dt ≤ C Σ_{n∈S} (T + n/q) |b_n|²`
for `T ≥ 1`. The spacing of `log n` near `n` is at least about `q/n` when `n ≥ q`, and at least
`log 2` otherwise, which `T ≥ 1` absorbs. -/
def MVOneClass : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ), 0 < q → ∀ (r : ZMod q) (S : Finset ℕ) (b : ℕ → ℂ) (T U : ℝ),
    1 ≤ T → (∀ n ∈ S, 0 < n ∧ (n : ZMod q) = r) →
    ∫ t in U..(U + T), ‖∑ n ∈ S, b n * (n : ℂ) ^ (-((t : ℂ) * Complex.I))‖ ^ 2
      ≤ C * ∑ n ∈ S, (T + n / q) * ‖b n‖ ^ 2

/-- LEAF: the Montgomery Vaughan mean value theorem for one residue class mod q, the analytic core
of Lemma 6, page 262, cited from Pan and Pan [9], which rests on Montgomery and Vaughan 1974,
Corollary 3 of the generalized Hilbert inequality. Class HARD. -/
theorem mv_one_class_leaf : MVOneClass := by
  sorry

/-- Orthogonality of the characters mod `q` in the form `Σ_χ χ⁻¹(s) χ(r) = φ(q) [s = r, s unit]`. -/
theorem char_inv_mul_sum_l6 (q : ℕ) [NeZero q] (r s : ZMod q) :
    ∑ χ : DirichletCharacter ℂ q, χ⁻¹ s * χ r =
      if s = r ∧ IsUnit s then (q.totient : ℂ) else 0 := by
  by_cases hs : IsUnit s
  · obtain ⟨u, rfl⟩ := hs
    have h1 : ∀ χ : DirichletCharacter ℂ q, χ⁻¹ (u : ZMod q) * χ r = χ (((u⁻¹ : (ZMod q)ˣ) :
        ZMod q) * r) := by
      intro χ
      rw [MulChar.inv_apply, Ring.inverse_unit, map_mul]
    simp only [h1, DirichletCharacter.sum_characters_eq, Units.inv_mul_eq_one]
    simp
  · have h0 : ∀ χ : DirichletCharacter ℂ q, χ⁻¹ s = 0 := fun χ => MulChar.map_nonunit _ hs
    simp [h0, hs]

/-- Orthogonality of characters, the first step of the proof of Lemma 6, page 262, PROVED:
`Σ_χ |Σ_r χ(r) B_r|² = φ(q) Σ_{r unit} |B_r|²`. -/
theorem char_orth_sq (q : ℕ) [NeZero q] (B : ZMod q → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ r, χ r * B r‖ ^ 2 =
      (q.totient : ℝ) * ∑ r ∈ univ.filter IsUnit, ‖B r‖ ^ 2 := by
  apply Complex.ofReal_injective
  have key : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
    intro z; rw [Complex.mul_conj']; push_cast; ring
  have hc : ∀ (χ : DirichletCharacter ℂ q) (s : ZMod q), (starRingEnd ℂ) (χ s) = χ⁻¹ s :=
    fun χ s => MulChar.star_apply' χ s
  rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_natCast]
  simp only [key, map_sum, map_mul, hc, Finset.sum_mul_sum]
  have e1 : ∀ χ : DirichletCharacter ℂ q, ∑ r, ∑ s, χ r * B r * (χ⁻¹ s * (starRingEnd ℂ) (B s)) =
      ∑ r, ∑ s, B r * (starRingEnd ℂ) (B s) * (χ⁻¹ s * χ r) := by
    intro χ; refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_; ring
  simp only [e1]
  rw [Finset.sum_comm]
  simp only [fun r => Finset.sum_comm (s := (univ : Finset (DirichletCharacter ℂ q)))
    (t := (univ : Finset (ZMod q))) (f := fun χ s => B r * (starRingEnd ℂ) (B s) * (χ⁻¹ s * χ r)),
    ← Finset.mul_sum, char_inv_mul_sum_l6]
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_eq_single r]
  · by_cases hr : IsUnit r <;> simp [hr]; ring
  · intro s _ hsr; simp [hsr]
  · simp

/-- Grouping by residue classes: `Σ_{n∈I} f(n) χ(n) = Σ_r χ(r) Σ_{n∈I, n≡r} f(n)`. -/
theorem fiber_char_sum_l6 (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (I : Finset ℕ) (f : ℕ → ℂ) :
    ∑ n ∈ I, f n * χ n = ∑ r, χ r * ∑ n ∈ I.filter (fun n : ℕ => (n : ZMod q) = r), f n := by
  rw [← Finset.sum_fiberwise I (fun n : ℕ => (n : ZMod q))]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [(Finset.mem_filter.1 hn).2]; ring

/-- Lemma 6, page 262, from the Montgomery Vaughan LEAF, PROVED: orthogonality reduces the sum
over `χ` to `φ(q)` times a sum over reduced classes, the LEAF bounds each class, and
`φ(q) (T + n/q) ≤ qT + n`. -/
theorem lemma6_of_mv (h : MVOneClass) : Lemma6 := by
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C, fun q _ M Nn c T U σ hT => ?_⟩
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set I := Finset.Icc (M + 1) (M + Nn) with hI
  have hpos : ∀ n ∈ I, 0 < n := fun n hn => by
    rw [hI, Finset.mem_Icc] at hn; omega
  set b : ℕ → ℂ := fun n => c n * (n : ℂ) ^ (-(σ : ℂ)) with hb
  set G : ZMod q → ℝ → ℝ := fun r t =>
    ‖∑ n ∈ I.filter (fun n : ℕ => (n : ZMod q) = r), b n * (n : ℂ) ^ (-((t : ℂ) * Complex.I))‖ ^ 2
    with hG
  have hpt : ∀ t : ℝ, ∑ χ : DirichletCharacter ℂ q,
      ‖∑ n ∈ I, c n * χ n * (n : ℂ) ^ (-((σ : ℂ) + t * Complex.I))‖ ^ 2 =
      (q.totient : ℝ) * ∑ r ∈ univ.filter IsUnit, G r t := by
    intro t
    have e : ∀ χ : DirichletCharacter ℂ q,
        ∑ n ∈ I, c n * χ n * (n : ℂ) ^ (-((σ : ℂ) + t * Complex.I)) =
        ∑ n ∈ I, (b n * (n : ℂ) ^ (-((t : ℂ) * Complex.I))) * χ n := by
      intro χ
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (hpos n hn).ne'
      rw [show -((σ : ℂ) + t * Complex.I) = -(σ : ℂ) + -((t : ℂ) * Complex.I) by ring,
        Complex.cpow_add _ _ hn0, hb]
      ring
    simp only [e, fiber_char_sum_l6]
    exact char_orth_sq q _
  have hcont : ∀ r, Continuous (G r) := by
    intro r
    refine Continuous.pow (Continuous.norm (continuous_finsetSum _ fun n hn => ?_)) 2
    have hn0 : (n : ℂ) ≠ 0 := by
      exact_mod_cast (hpos n (Finset.mem_filter.1 hn).1).ne'
    exact continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hn0))
  rw [intervalIntegral.integral_congr (g := fun t => (q.totient : ℝ) *
      ∑ r ∈ univ.filter IsUnit, G r t) (fun t _ => hpt t)]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun r _ => (hcont r).intervalIntegrable _ _)]
  have hbn : ∀ n ∈ I, ‖b n‖ ^ 2 = ‖c n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
    intro n hn
    rw [hb]
    simp only
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (hpos n hn), mul_pow]
    congr 1
    simp only [Complex.neg_re, Complex.ofReal_re]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    ring_nf
  set F : ℕ → ℝ := fun n => (T + n / q) * ‖b n‖ ^ 2 with hF
  have hF0 : ∀ n, 0 ≤ F n := fun n => by
    rw [hF]; have : (0 : ℝ) ≤ n / q := by positivity
    have : 0 ≤ T := by linarith
    positivity
  have step1 : ∑ r ∈ univ.filter IsUnit, ∫ t in U..(U + T), G r t ≤
      ∑ r ∈ univ.filter IsUnit, C * ∑ n ∈ I.filter (fun n : ℕ => (n : ZMod q) = r), F n := by
    refine Finset.sum_le_sum fun r _ => ?_
    exact hC q hq r _ b T U hT fun n hn =>
      ⟨hpos n (Finset.mem_filter.1 hn).1, (Finset.mem_filter.1 hn).2⟩
  have step2 : ∑ r ∈ univ.filter IsUnit, C * ∑ n ∈ I.filter (fun n : ℕ => (n : ZMod q) = r), F n ≤
      C * ∑ n ∈ I, F n := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hC0
    rw [← Finset.sum_fiberwise I (fun n : ℕ => (n : ZMod q)) F]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun r _ _ => Finset.sum_nonneg fun n _ => hF0 n
  have htot : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have htot0 : (0 : ℝ) ≤ q.totient := by positivity
  have step3 : (q.totient : ℝ) * (C * ∑ n ∈ I, F n) ≤
      C * ∑ n ∈ I, (q * T + n) * ‖c n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
    rw [mul_left_comm, Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n hn => ?_) hC0
    rw [hF]
    simp only
    rw [hbn n hn]
    have hX : 0 ≤ ‖c n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by positivity
    have hk : (q.totient : ℝ) * (T + n / q) ≤ q * T + n := by
      have hT0 : 0 ≤ T := by linarith
      have h1 : (q.totient : ℝ) * T ≤ q * T := mul_le_mul_of_nonneg_right htot hT0
      have h2 : (q.totient : ℝ) * (n / q) ≤ n := by
        rw [mul_div_assoc', div_le_iff₀ hqR]
        exact mul_le_mul_of_nonneg_left htot (Nat.cast_nonneg n) |>.trans_eq' (by ring)
      nlinarith
    calc (q.totient : ℝ) * ((T + n / q) * (‖c n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)))
        = ((q.totient : ℝ) * (T + n / q)) * (‖c n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) := by ring
      _ ≤ (q * T + n) * (‖c n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) := mul_le_mul_of_nonneg_right hk hX
      _ = (q * T + n) * ‖c n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by ring
  calc (q.totient : ℝ) * ∑ r ∈ univ.filter IsUnit, ∫ t in U..(U + T), G r t
      ≤ (q.totient : ℝ) * (C * ∑ n ∈ I, F n) :=
        mul_le_mul_of_nonneg_left (step1.trans step2) htot0
    _ ≤ _ := step3

/-- Lemma 6, page 262, PROVED from the single cited LEAF `mv_one_class_leaf`. -/
theorem zhan_lemma6_split : Lemma6 := lemma6_of_mv mv_one_class_leaf

end

end LeanLab.Zhan1991

#print axioms LeanLab.Zhan1991.char_orth_sq
#print axioms LeanLab.Zhan1991.lemma6_of_mv
#print axioms LeanLab.Zhan1991.zhan_lemma6_split
