/-
P0069, page 12, the finite Hilbert space step behind the large value argument.
Source: Huxley, On the Difference between Consecutive Primes, Section 2,
Inventiones Mathematicae 15, pages 165 and 166, displays 2.5 to 2.9.
https://doi.org/10.1007/BF01418933
The hybrid analytic weight estimate is not supplied by these elementary steps.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.MeanSquareC165

namespace LeanLab.BHP1997.Decomp492b
open Complex
open scoped ComplexConjugate

/-- Huxley page 165, display 2.5, auxiliary finite Gram estimate.
Coefficients of norm at most one bound the squared norm of their vector sum
by the sum of the absolute Gram entries. -/
theorem norm_sum_smul_sq_le_gram {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (S : Finset ι) (y : ι → E) (c : ι → ℂ)
    (hc : ∀ r ∈ S, ‖c r‖ ≤ 1) :
    ‖∑ r ∈ S, c r • y r‖ ^ 2 ≤ ∑ r ∈ S, ∑ s ∈ S, ‖inner ℂ (y r) (y s)‖ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  calc
    (∑ r ∈ S, ∑ s ∈ S, conj (c r) * (c s * inner ℂ (y r) (y s))).re
      ≤ ‖∑ r ∈ S, ∑ s ∈ S, conj (c r) * (c s * inner ℂ (y r) (y s))‖ := re_le_norm _
    _ ≤ ∑ r ∈ S, ∑ s ∈ S, ‖conj (c r) * (c s * inner ℂ (y r) (y s))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => norm_sum_le _ _)
    _ ≤ ∑ r ∈ S, ∑ s ∈ S, ‖inner ℂ (y r) (y s)‖ := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro s hs
      simp only [norm_mul, norm_conj]
      exact (mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (norm_nonneg _) (hc s hs)) (norm_nonneg _)).trans
          (mul_le_of_le_one_left (norm_nonneg _) (hc r hr))

/-- Huxley page 165, display 2.5, auxiliary choice of phases.
Every complex value has a multiplier of norm at most one making it real and nonnegative. -/
theorem exists_phase (z : ℂ) : ∃ u : ℂ, ‖u‖ ≤ 1 ∧ u * z = (‖z‖ : ℂ) := by
  obtain ⟨u, hu, hz⟩ := Complex.exists_norm_eq_mul_self z
  exact ⟨u, hu.le, hz.symm⟩

/-- Huxley page 165, display 2.5, finite Hilbert space form of the Halasz inequality.
The Gram sum still needs the separate analytic estimate in display 2.6. -/
theorem halasz_inequality {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (S : Finset ι) (x : E) (y : ι → E) {V : ℝ}
    (hV : 0 ≤ V) (hpoint : ∀ r ∈ S, V ≤ ‖inner ℂ x (y r)‖) :
    (S.card : ℝ) ^ 2 * V ^ 2 ≤
      ‖x‖ ^ 2 * ∑ r ∈ S, ∑ s ∈ S, ‖inner ℂ (y r) (y s)‖ := by
  choose c hc hphase using fun r => exists_phase (inner ℂ x (y r))
  let w := ∑ r ∈ S, c r • y r
  have heq : inner ℂ x w = ((∑ r ∈ S, ‖inner ℂ x (y r)‖ : ℝ) : ℂ) := by
    simp only [w, inner_sum, inner_smul_right, hphase, ofReal_sum]
  have hsum : (S.card : ℝ) * V ≤ ∑ r ∈ S, ‖inner ℂ x (y r)‖ := by
    simpa only [nsmul_eq_mul] using Finset.card_nsmul_le_sum S _ V hpoint
  have hsq := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hV) hsum 2
  have hnorm : ∑ r ∈ S, ‖inner ℂ x (y r)‖ ≤ ‖x‖ * ‖w‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) x w
    rw [heq, norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun r hr => norm_nonneg _)] at h
    exact h
  have hcs := pow_le_pow_left₀ (Finset.sum_nonneg fun r hr => norm_nonneg (inner ℂ x (y r))) hnorm 2
  have hgram := norm_sum_smul_sq_le_gram S y c (fun r _ => hc r)
  calc
    (S.card : ℝ) ^ 2 * V ^ 2 = ((S.card : ℝ) * V) ^ 2 := (mul_pow _ _ _).symm
    _ ≤ (∑ r ∈ S, ‖inner ℂ x (y r)‖) ^ 2 := hsq
    _ ≤ (‖x‖ * ‖w‖) ^ 2 := hcs
    _ = ‖x‖ ^ 2 * ‖w‖ ^ 2 := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hgram (sq_nonneg _)

/-- Huxley page 165, display 2.5, the weighted finite coefficient form.
The weights are at least one. The phases and Cauchy Schwarz step are fully proved.
The analytic selection of weights in display 2.6 is a separate missing input. -/
theorem weighted_halasz {ι ν : Type*} [Fintype ν] (S : Finset ι)
    (a : ν → ℂ) (f : ι → ν → ℂ) (b : ν → ℝ) (hb : ∀ n, 1 ≤ b n)
    {V : ℝ} (hV : 0 ≤ V) (hpoint : ∀ r ∈ S, V ≤ ‖∑ n, a n * f r n‖) :
    (S.card : ℝ) ^ 2 * V ^ 2 ≤
      (∑ n, ‖a n‖ ^ 2) *
        ∑ r ∈ S, ∑ s ∈ S, ‖∑ n, (b n : ℂ) * conj (f r n) * f s n‖ := by
  classical
  let x : EuclideanSpace ℂ ν := WithLp.toLp 2 (fun n => conj (a n) / (Real.sqrt (b n) : ℂ))
  let y : ι → EuclideanSpace ℂ ν := fun r => WithLp.toLp 2
    (fun n => (Real.sqrt (b n) : ℂ) * f r n)
  have hb0 (n : ν) : 0 < b n := lt_of_lt_of_le zero_lt_one (hb n)
  have hsqrt (n : ν) : (Real.sqrt (b n) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (hb0 n)))
  have heval (r : ι) : inner ℂ x (y r) = ∑ n, a n * f r n := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [x, y, RCLike.inner_apply, map_div₀,
      conj_conj, conj_ofReal]
    field_simp [hsqrt n]
  have hgram (r s : ι) : inner ℂ (y r) (y s) =
      ∑ n, (b n : ℂ) * conj (f r n) * f s n := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [y, RCLike.inner_apply, map_mul, conj_ofReal]
    have hsq : (Real.sqrt (b n) : ℂ) ^ 2 = (b n : ℂ) := by
      exact_mod_cast Real.sq_sqrt (hb0 n).le
    calc
      (↑(Real.sqrt (b n)) * f s n) * (↑(Real.sqrt (b n)) * conj (f r n)) =
          (Real.sqrt (b n) : ℂ) ^ 2 * conj (f r n) * f s n := by ring
      _ = _ := by rw [hsq]
  have henergy : ‖x‖ ^ 2 ≤ ∑ n, ‖a n‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro n hn
    simp only [x, norm_div, norm_conj, norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), div_pow,
      Real.sq_sqrt (hb0 n).le]
    exact div_le_self (sq_nonneg _) (hb n)
  have h := halasz_inequality S x y hV (by simpa only [heval] using hpoint)
  simp_rw [hgram] at h
  exact h.trans (mul_le_mul_of_nonneg_right henergy
    (Finset.sum_nonneg fun r hr => Finset.sum_nonneg fun s hs => norm_nonneg _))

/-- Huxley page 166, display 2.9, finite time subdivision.
If every half-open interval of positive length H contains at most A members,
a family in the interval from minus T to T has at most 2T/H plus one times A members.
This is an elementary implication from the explicit local counting hypothesis. -/
theorem card_le_of_local_intervals {ι : Type*} (S : Finset ι) (t : ι → ℝ)
    {T H A : ℝ} (hT : 0 ≤ T) (hH : 0 < H) (hA : 0 ≤ A)
    (ht : ∀ r ∈ S, |t r| ≤ T)
    (hlocal : ∀ u : ℝ, ((S.filter (fun r => u ≤ t r ∧ t r < u + H)).card : ℝ) ≤ A) :
    (S.card : ℝ) ≤ (2 * T / H + 1) * A := by
  classical
  let J := Finset.range (⌊2 * T / H⌋₊ + 1)
  let k : ι → ℕ := fun r => ⌊(t r + T) / H⌋₊
  have hmaps : ∀ r ∈ S, k r ∈ J := by
    intro r hr
    have ht' := abs_le.mp (ht r hr)
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.floor_le_floor
      (div_le_div_of_nonneg_right (by linarith : t r + T ≤ 2 * T) hH.le))
  have hfiber (j : ℕ) : ((S.filter (fun r => k r = j)).card : ℝ) ≤ A := by
    have hsub : S.filter (fun r => k r = j) ⊆
        S.filter (fun r => (j : ℝ) * H - T ≤ t r ∧ t r < (j : ℝ) * H - T + H) := by
      intro r hr
      obtain ⟨hr, hk⟩ := Finset.mem_filter.mp hr
      have ht' := abs_le.mp (ht r hr)
      have hn : 0 ≤ (t r + T) / H := div_nonneg (by linarith) hH.le
      have hlo := Nat.floor_le hn
      have hhi := Nat.lt_floor_add_one ((t r + T) / H)
      change (⌊(t r + T) / H⌋₊ : ℕ) = j at hk
      rw [hk] at hlo hhi
      refine Finset.mem_filter.mpr ⟨hr, ?_, ?_⟩
      · have := (le_div_iff₀ hH).mp hlo
        linarith
      · have := (div_lt_iff₀ hH).mp hhi
        nlinarith
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hlocal _)
  have hcard : (S.card : ℝ) = ∑ j ∈ J, ((S.filter (fun r => k r = j)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  rw [hcard]
  calc
    _ ≤ ∑ _j ∈ J, A := Finset.sum_le_sum (fun j hj => hfiber j)
    _ = (⌊2 * T / H⌋₊ + 1 : ℕ) * A := by simp [J]
    _ ≤ (2 * T / H + 1) * A := by
      apply mul_le_mul_of_nonneg_right _ hA
      push_cast
      linarith [Nat.floor_le (div_nonneg (by linarith : 0 ≤ 2 * T) hH.le)]

/-- Huxley page 166, displays 2.7 and 2.8, threshold absorption.
This finite algebra step keeps the required positive threshold V. -/
theorem count_le_of_quadratic_bound {R G F D V : ℝ}
    (hR : 0 ≤ R) (hV : 0 < V) (hGF : 0 ≤ G * F)
    (hbound : R ^ 2 * V ^ 2 ≤ G * (R * F + R ^ 2 * D))
    (hsmall : G * D ≤ V ^ 2 / 2) : R ≤ 2 * G * F / V ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hV)).mpr
  rcases eq_or_lt_of_le hR with hzero | hpos
  · rw [← hzero]
    nlinarith
  · have hs := mul_le_mul_of_nonneg_left hsmall (sq_nonneg R)
    have hh : R * (R * V ^ 2) ≤ R * (2 * G * F) := by nlinarith
    exact (mul_le_mul_iff_right₀ hpos).mp (by nlinarith [hh])

/-- Huxley page 166, equality case of display 2.8 with an explicit absolute constant.
The local interval length is V to the fourth divided by 4 C squared G squared L squared. -/
theorem huxley_cut_scale {C G L V : ℝ}
    (hC : 0 < C) (hG : 0 < G) (hL : 0 < L) (hV : 0 < V) :
    Real.sqrt (V ^ 4 / (4 * C ^ 2 * G ^ 2 * L ^ 2)) = V ^ 2 / (2 * C * G * L) := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  field_simp [hC.ne', hG.ne', hL.ne', hV.ne']
  ring

/-- Huxley page 166, display 2.9, exact algebra after choosing the local interval length. -/
theorem huxley_cut_identity {C G L V : ℝ} (hC : 0 < C) (hG : 0 < G)
    (hL : 0 < L) (hV : 0 < V) (F T : ℝ) :
    (2 * T / (V ^ 4 / (4 * C ^ 2 * G ^ 2 * L ^ 2)) + 1) * (2 * C * G * F / V ^ 2) =
      2 * C * G * F / V ^ 2 + 16 * C ^ 3 * G ^ 3 * F * T * L ^ 2 / V ^ 6 := by
  field_simp [hC.ne', hG.ne', hL.ne', hV.ne']
  ring

/-- Huxley page 166, display 2.9, subdivision from the local Halasz kernel bound.
CONDITIONAL ON the displayed local bound. This is the untwisted time subdivision.
It asserts no hybrid character estimate and imports no cited analytic result. -/
theorem huxley_subdivision {ι : Type*} (S : Finset ι) (t : ι → ℝ)
    {C G L V F T : ℝ} (hC : 0 < C) (hG : 0 < G) (hL : 0 < L) (hV : 0 < V)
    (hF : 0 ≤ F) (hT : 0 ≤ T) (ht : ∀ r ∈ S, |t r| ≤ T)
    (hlocal : ∀ u : ℝ,
      let H := V ^ 4 / (4 * C ^ 2 * G ^ 2 * L ^ 2)
      let R : ℝ := ((S.filter (fun r => u ≤ t r ∧ t r < u + H)).card : ℝ)
      R ^ 2 * V ^ 2 ≤ C * G * (R * F + R ^ 2 * (Real.sqrt H * L))) :
    (S.card : ℝ) ≤ 2 * C * G * F / V ^ 2 +
      16 * C ^ 3 * G ^ 3 * F * T * L ^ 2 / V ^ 6 := by
  classical
  let H := V ^ 4 / (4 * C ^ 2 * G ^ 2 * L ^ 2)
  have hH : 0 < H := by dsimp [H]; positivity
  have hsmall : (C * G) * (Real.sqrt H * L) ≤ V ^ 2 / 2 := by
    rw [show Real.sqrt H = V ^ 2 / (2 * C * G * L) from huxley_cut_scale hC hG hL hV]
    have : (C * G) * (V ^ 2 / (2 * C * G * L) * L) = V ^ 2 / 2 := by field_simp
    exact this.le
  have hlocalCount : ∀ u : ℝ,
      ((S.filter (fun r => u ≤ t r ∧ t r < u + H)).card : ℝ) ≤ 2 * C * G * F / V ^ 2 := by
    intro u
    simpa only [H, mul_assoc] using
      count_le_of_quadratic_bound (Nat.cast_nonneg _) hV (by positivity) (hlocal u) hsmall
  have h := card_le_of_local_intervals S t hT hH (by positivity) ht hlocalCount
  rwa [huxley_cut_identity hC hG hL hV F T] at h

/-- BHP pages 11 and 12, display 3.4, the exact finite Halasz reduction for its polynomial.
Huxley page 165 display 2.5 supplies the finite matrix argument. The remaining double Gram
sum is the genuine analytic kernel to estimate. No spacing or analytic bound is assumed here. -/
theorem hybrid_halasz_gram {q : ℕ} (S : Finset (ℝ × DirichletCharacter ℂ q))
    (a : ℕ → ℂ) (b : ℕ → ℝ) (c1 c2 F : ℝ) (hlo : 0 < c1 * F)
    (hb : ∀ n : ℕ, c1 * F < n → (n : ℝ) < c2 * F → 1 ≤ b n)
    {V : ℝ} (hV : 0 ≤ V)
    (hpoint : ∀ p ∈ S, V ≤ ‖Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1)‖) :
    (S.card : ℝ) ^ 2 * V ^ 2 ≤ MeanSquareC165.energy a c1 c2 F *
      ∑ p ∈ S, ∑ r ∈ S,
        ‖∑ n ∈ (Finset.range (⌊c2 * F⌋₊ + 1)).filter
            (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F),
          (b n : ℂ) * (n : ℂ) *
            conj (p.2 (n : ZMod q) / (n : ℂ) ^ Thm4.half p.1) *
              (r.2 (n : ZMod q) / (n : ℂ) ^ Thm4.half r.1)‖ := by
  classical
  let J := (Finset.range (⌊c2 * F⌋₊ + 1)).filter
    (fun n : ℕ => c1 * F < n ∧ (n : ℝ) < c2 * F)
  let α : J → ℂ := fun n => a n / (Real.sqrt (n : ℝ) : ℂ)
  let f : (ℝ × DirichletCharacter ℂ q) → J → ℂ :=
    fun p n => (Real.sqrt (n : ℝ) : ℂ) *
      (p.2 (n : ZMod q) / (n : ℂ) ^ Thm4.half p.1)
  have hnpos (n : J) : 0 < (n : ℝ) :=
    hlo.trans (Finset.mem_filter.mp n.property).2.1
  have hsqrt (n : J) : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (hnpos n)))
  have heval (p : ℝ × DirichletCharacter ℂ q) :
      (∑ n : J, α n * f p n) = Thm4.dirPoly a c1 c2 F p.2 (Thm4.half p.1) := by
    calc
      _ = ∑ n : J, a n * p.2 (n : ZMod q) / (n : ℂ) ^ Thm4.half p.1 := by
        apply Finset.sum_congr rfl
        intro n hn
        dsimp only [α, f]
        rw [← mul_assoc, div_mul_cancel₀ _ (hsqrt n)]
        ring
      _ = _ := by
        simpa only [Thm4.dirPoly, J] using
          (Finset.sum_coe_sort J (fun n : ℕ => a n * p.2 (n : ZMod q) /
            (n : ℂ) ^ Thm4.half p.1))
  have henergy : (∑ n : J, ‖α n‖ ^ 2) = MeanSquareC165.energy a c1 c2 F := by
    calc
      _ = ∑ n : J, ‖a n‖ ^ 2 / (n : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [α, norm_div, norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt (hnpos n).le]
      _ = _ := by
        simpa only [MeanSquareC165.energy, J] using
          (Finset.sum_coe_sort J (fun n : ℕ => ‖a n‖ ^ 2 / (n : ℝ)))
  have hgram (p r : ℝ × DirichletCharacter ℂ q) :
      (∑ n : J, (b n : ℂ) * conj (f p n) * f r n) =
        ∑ n ∈ J, (b n : ℂ) * (n : ℂ) *
          conj (p.2 (n : ZMod q) / (n : ℂ) ^ Thm4.half p.1) *
            (r.2 (n : ZMod q) / (n : ℂ) ^ Thm4.half r.1) := by
    calc
      _ = ∑ n : J, (b n : ℂ) * (n : ℂ) *
          conj (p.2 (n : ZMod q) / (n : ℂ) ^ Thm4.half p.1) *
            (r.2 (n : ZMod q) / (n : ℂ) ^ Thm4.half r.1) := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [f, map_mul, conj_ofReal]
        have hsq : (Real.sqrt (n : ℝ) : ℂ) ^ 2 = (n : ℂ) := by
          exact_mod_cast Real.sq_sqrt (hnpos n).le
        calc
          _ = (b n : ℂ) * (Real.sqrt (n : ℝ) : ℂ) ^ 2 *
              conj (p.2 (n : ZMod q) / (n : ℂ) ^ Thm4.half p.1) *
                (r.2 (n : ZMod q) / (n : ℂ) ^ Thm4.half r.1) := by ring
          _ = _ := by rw [hsq]
      _ = _ := Finset.sum_coe_sort J (fun n : ℕ => (b n : ℂ) * (n : ℂ) *
        conj (p.2 (n : ZMod q) / (n : ℂ) ^ Thm4.half p.1) *
          (r.2 (n : ZMod q) / (n : ℂ) ^ Thm4.half r.1))
  have h := weighted_halasz S α f (fun n : J => b n)
    (fun n => hb n (Finset.mem_filter.mp n.property).2.1 (Finset.mem_filter.mp n.property).2.2)
    hV (by simpa only [heval] using hpoint)
  simpa only [henergy, hgram] using h

/-- BHP page 12 preliminary display and Huxley page 166 display 2.9, route diagnostic.
If the diagonal length term also carries L, the same direct cut yields L cubed in the
sixth-power term. This records a weaker bound, not a paper error. -/
theorem extra_log_cut_identity {C G L V : ℝ} (hC : 0 < C) (hG : 0 < G)
    (hL : 0 < L) (hV : 0 < V) (F T : ℝ) :
    (2 * T / (V ^ 4 / (4 * C ^ 2 * G ^ 2 * L ^ 2)) + 1) * (2 * C * L * G * F / V ^ 2) =
      2 * C * L * G * F / V ^ 2 + 16 * C ^ 3 * G ^ 3 * F * T * L ^ 3 / V ^ 6 := by
  calc
    _ = L * ((2 * T / (V ^ 4 / (4 * C ^ 2 * G ^ 2 * L ^ 2)) + 1) *
        (2 * C * G * F / V ^ 2)) := by ring
    _ = L * (2 * C * G * F / V ^ 2 + 16 * C ^ 3 * G ^ 3 * F * T * L ^ 2 / V ^ 6) :=
      congrArg (fun u => L * u) (huxley_cut_identity hC hG hL hV F T)
    _ = _ := by ring

/-- BHP page 12 and Huxley page 166, auxiliary loss diagnostic.
The logarithm cubed loss of the direct weaker cut cannot be absorbed by a uniform constant
into logarithm squared. This does not refute either original hybrid estimate. -/
theorem extra_log_not_absorbable (K : ℝ) :
    ∃ x : ℝ, Real.exp 1 ≤ x ∧ K * Real.log x ^ 2 < Real.log x ^ 3 := by
  let L := |K| + 2
  have hL : 0 < L := by dsimp [L]; positivity
  have hKL : K < L := by dsimp [L]; linarith [le_abs_self K]
  refine ⟨Real.exp L, Real.exp_le_exp.mpr (by dsimp [L]; linarith [abs_nonneg K]), ?_⟩
  rw [Real.log_exp]
  calc
    K * L ^ 2 < L * L ^ 2 := mul_lt_mul_of_pos_right hKL (sq_pos_of_pos hL)
    _ = L ^ 3 := by ring

end LeanLab.BHP1997.Decomp492b






