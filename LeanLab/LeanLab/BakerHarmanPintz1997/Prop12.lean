/-
P0069, pages 1 to 3. The vector sieve deduction of equation 1.2.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.Deductions
import LeanLab.ChenExplicit.Reductions

namespace LeanLab.BakerHarmanPintz1997
open Real Filter Topology
attribute [local instance] Classical.propDecidable

/-- The prime indicator of page 1. -/
noncomputable def primeIndicator (n : ℕ) : ℝ := if n.Prime then 1 else 0

/-- Equation 1.2 is the prime indicator convolution on the two intervals. -/
theorem Scount_eq_convIJ (ε x : ℝ) (N : ℕ) (hx : 0 ≤ x) :
    (Scount ε x N : ℝ) = convIJ ε x primeIndicator primeIndicator N := by
  have hY : 0 ≤ Yof ε x := Real.rpow_nonneg hx _
  unfold Scount convIJ Iset Jset primeIndicator
  rw [Finset.sum_filter]
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  have hJ : N - k ∈ Finset.Ioc ⌊Yof ε x⌋₊ ⌊2 * Yof ε x⌋₊ ↔
      Yof ε x < ((N - k : ℕ) : ℝ) ∧ ((N - k : ℕ) : ℝ) ≤ 2 * Yof ε x := by
    simp only [Finset.mem_Ioc, Nat.floor_lt hY, Nat.le_floor_iff (by positivity : 0 ≤ 2 * Yof ε x)]
  simp only [hJ]
  by_cases h : k ≤ N <;> by_cases hp : k.Prime <;>
    by_cases hq : (N - k).Prime <;> simp [h, hp, hq]

/-- The hypotheses on an I sequence in Theorem 2, page 3. -/
structure ISequence (ε : ℝ) (a : ℝ → ℕ → ℝ) (u B : ℝ) : Prop where
  positive : 0 < u
  distribution : ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x → ∀ t : ℝ, t ≤ x →
    ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ L x ^ A → ∀ χ : DirichletCharacter ℂ q,
      ‖∑ k ∈ (Iset ε x).filter (fun k : ℕ => (k : ℝ) ≤ t),
        ((a x k : ℂ) * χ (k : ZMod q) - ((delta χ * u / L x : ℝ) : ℂ))‖ ≤
        C * Yof ε x / L x ^ A
  divisor_bound : ∃ C : ℝ, ∀ x k, |a x k| ≤ C * tau k ^ B
  rough_support : ∀ A : ℝ, 0 < A → Ev fun x => ∀ k, a x k ≠ 0 → Rough k (L x ^ A)

/-- The hypotheses on a J sequence in Theorem 2, page 3. -/
structure JSequence (ε : ℝ) (b : ℝ → ℕ → ℝ) (v B : ℝ)
    (Ex : ℝ → ∀ q : ℕ, Finset (DirichletCharacter ℂ q)) : Prop where
  positive : 0 < v
  divisor_bound : ∃ C : ℝ, ∀ x m, |b x m| ≤ C * tau m ^ B
  distribution : ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x → ∀ t : ℝ, t ≤ 2 * Yof ε x →
    ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ L x ^ A → ∀ χ : DirichletCharacter ℂ q,
      ‖∑ m ∈ (Jset ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        ((b x m : ℂ) * χ (m : ZMod q) - ((delta χ * v / Real.log (Yof ε x) : ℝ) : ℂ))‖ ≤
        C * Yof ε x / L x ^ A
  mean_square : ∀ A : ℝ, 0 < A → ∃ C X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
    (∀ q : ℕ, ((Ex x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) / L x ^ (2 * A)) ∧
    ∀ (q : ℕ) [NeZero q], q ≤ Qof ε x → ∀ z : ℝ, q * Qof ε x / (6 * Yof ε x) ≤ z →
      z ≤ 6 * q * Qof ε x / Yof ε x →
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ∉ Ex x q),
        ∫ y in (Yof ε x / 2)..(3 * Yof ε x),
          ‖∑ m ∈ Jy y z, ((b x m : ℂ) * χ (m : ZMod q) -
            ((delta χ * v / Real.log (Yof ε x) : ℝ) : ℂ))‖ ^ 2 ≤
        C * ((q : ℝ) * Qof ε x) ^ 2 * Yof ε x / L x ^ A

/-- The common positive main factor in equation 1.6, page 2. -/
noncomputable def sieveMain (ε x : ℝ) (N : ℕ) : ℝ :=
  Yof ε x / (L x * Real.log (Yof ε x)) * SS N

/-- The finite exceptional set for equation 1.6, page 3. -/
noncomputable def sieveBad (ε x : ℝ) (a b : ℕ → ℝ) (u v C : ℝ) : Finset ℕ :=
  (Finset.Icc ⌈x⌉₊ ⌊x + x ^ (theta1 ε * theta2)⌋₊).filter (fun N => Even N ∧
    C * |u * v * sieveMain ε x N| / L x <
      |convIJ ε x a b N - u * v * sieveMain ε x N|)

/-- Apply the cited Theorem 2 to one admissible sequence pair. -/
theorem sieveBad_bound {ε : ℝ} (hT : Theorem2 ε)
    {a b : ℝ → ℕ → ℝ} {u v B : ℝ}
    {Ex : ℝ → ∀ q : ℕ, Finset (DirichletCharacter ℂ q)}
    (ha : ISequence ε a u B) (hb : JSequence ε b v B Ex) :
    ∃ C : ℝ, ∀ A : ℝ, 0 < A → ∃ X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
      ((sieveBad ε x (a x) (b x) u v C).card : ℝ) <
        x ^ (theta1 ε * theta2) / L x ^ A := by
  have h := hT a b u v B Ex ha.positive hb.positive ha.distribution
    ha.divisor_bound hb.divisor_bound ha.rough_support hb.distribution hb.mean_square
  simpa only [sieveBad, sieveMain, mul_div_assoc, mul_assoc] using h

/-- The singular series is positive, as used on page 2. -/
theorem SS_pos (N : ℕ) : 0 < SS N := by
  have h := LeanLab.PerelliPintz1992.S2k_ge (N / 2)
  have ht := LeanLab.ChenExplicit.twinC_pos
  change 0 < LeanLab.PerelliPintz1992.S2k (N / 2)
  linarith

/-- The common main factor in equation 1.6 is positive for x greater than 1. -/
theorem sieveMain_pos {ε x : ℝ} (hε : 0 ≤ ε) (hx : 1 < x) (N : ℕ) :
    0 < sieveMain ε x N := by
  have ht : 0 < theta1 ε := by unfold theta1; linarith
  have hY : 0 < Yof ε x := Real.rpow_pos_of_pos (by linarith) _
  have hlogY : 0 < Real.log (Yof ε x) := by
    rw [Yof, Real.log_rpow (by linarith : 0 < x)]
    exact mul_pos ht (Real.log_pos hx)
  exact mul_pos (div_pos hY (mul_pos (Real.log_pos hx) hlogY)) (SS_pos N)

/-- The error terms in the three applications of equation 1.6 preserve a positive margin. -/
theorem vector_main_positive {M l p q r C01 C10 C11 S01 S10 S11 : ℝ}
    (hM : 0 < M) (hl : 0 < l) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hmargin : |C01| * p + |C10| * q + |C11| * r < (p + q - r) * l)
    (h01 : |S01 - p * M| ≤ C01 * |p * M| / l)
    (h10 : |S10 - q * M| ≤ C10 * |q * M| / l)
    (h11 : |S11 - r * M| ≤ C11 * |r * M| / l) :
    0 < S01 + S10 - S11 := by
  rw [abs_of_nonneg (mul_nonneg hp hM.le)] at h01
  rw [abs_of_nonneg (mul_nonneg hq hM.le)] at h10
  rw [abs_of_nonneg (mul_nonneg hr hM.le)] at h11
  have h01' : (p * M - S01) * l ≤ |C01| * p * M := by
    calc (p * M - S01) * l ≤ |S01 - p * M| * l := by
          apply mul_le_mul_of_nonneg_right _ hl.le
          linarith [neg_le_abs (S01 - p * M)]
      _ ≤ C01 * (p * M) := (le_div_iff₀ hl).mp h01
      _ ≤ |C01| * p * M := by
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_right (le_abs_self C01) (mul_nonneg hp hM.le)
  have h10' : (q * M - S10) * l ≤ |C10| * q * M := by
    calc (q * M - S10) * l ≤ |S10 - q * M| * l := by
          apply mul_le_mul_of_nonneg_right _ hl.le
          linarith [neg_le_abs (S10 - q * M)]
      _ ≤ C10 * (q * M) := (le_div_iff₀ hl).mp h10
      _ ≤ |C10| * q * M := by
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_right (le_abs_self C10) (mul_nonneg hq hM.le)
  have h11' : (S11 - r * M) * l ≤ |C11| * r * M := by
    calc (S11 - r * M) * l ≤ |S11 - r * M| * l :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hl.le
      _ ≤ C11 * (r * M) := (le_div_iff₀ hl).mp h11
      _ ≤ |C11| * r * M := by
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_right (le_abs_self C11) (mul_nonneg hr hM.le)
  have hstrict := mul_lt_mul_of_pos_right hmargin hM
  have hsum : 0 < (S01 + S10 - S11) * l := by nlinarith only [h01', h10', h11', hstrict]
  exact pos_of_mul_pos_left hsum hl.le

/-- Equations 1.3 and 1.4, for the four sequence families of Sections 4 and 5. -/
def VectorSieveBounds (ε : ℝ) (a0 a1 b0 b1 : ℝ → ℕ → ℝ) : Prop :=
  Ev fun x =>
    (∀ k ∈ Iset ε x, a0 x k ≤ primeIndicator k ∧ primeIndicator k ≤ a1 x k) ∧
    (∀ m ∈ Jset ε x, b0 x m ≤ primeIndicator m ∧ primeIndicator m ≤ b1 x m)

/-- Equation 1.2 from Theorem 2 and the four sequence hypotheses of Sections 4 and 5.
CONDITIONAL ON Theorem2 and the explicit sequence hypotheses only. -/
theorem prop12_of_theorem2 {ε : ℝ} (hε : 0 ≤ ε) (hT : Theorem2 ε)
    (a0 a1 b0 b1 : ℝ → ℕ → ℝ) (u0 u1 v0 v1 B : ℝ)
    (Ex0 Ex1 : ℝ → ∀ q : ℕ, Finset (DirichletCharacter ℂ q))
    (ha0 : ISequence ε a0 u0 B) (ha1 : ISequence ε a1 u1 B)
    (hb0 : JSequence ε b0 v0 B Ex0) (hb1 : JSequence ε b1 v1 B Ex1)
    (hsieve : VectorSieveBounds ε a0 a1 b0 b1)
    (hmargin : 0 < u0 * v1 + u1 * v0 - u1 * v1) : Prop12 ε := by
  obtain ⟨C01, h01⟩ := sieveBad_bound hT ha0 hb1
  obtain ⟨C10, h10⟩ := sieveBad_bound hT ha1 hb0
  obtain ⟨C11, h11⟩ := sieveBad_bound hT ha1 hb1
  obtain ⟨Xs, hXs⟩ := hsieve
  let D := u0 * v1 + u1 * v0 - u1 * v1
  let K := |C01| * (u0 * v1) + |C10| * (u1 * v0) + |C11| * (u1 * v1)
  have hD : 0 < D := hmargin
  intro A hA
  obtain ⟨X01, hX01⟩ := h01 (A + 1) (by linarith)
  obtain ⟨X10, hX10⟩ := h10 (A + 1) (by linarith)
  obtain ⟨X11, hX11⟩ := h11 (A + 1) (by linarith)
  have ev : ∀ᶠ x : ℝ in atTop,
      Xs ≤ x ∧ X01 ≤ x ∧ X10 ≤ x ∧ X11 ≤ x ∧ 2 ≤ x ∧ 3 ≤ L x ∧ K / D < L x := by
    exact (eventually_ge_atTop Xs).and ((eventually_ge_atTop X01).and
      ((eventually_ge_atTop X10).and ((eventually_ge_atTop X11).and
      ((eventually_ge_atTop 2).and ((Real.tendsto_log_atTop.eventually_ge_atTop 3).and
      (Real.tendsto_log_atTop.eventually_gt_atTop (K / D)))))))
  obtain ⟨X, hX⟩ := ev.exists_forall_of_atTop
  refine ⟨X, fun x hx => ?_⟩
  obtain ⟨hxs, hx01, hx10, hx11, hx2, hl3, hlK⟩ := hX x hx
  have hxpos : 0 < x := by linarith
  have hl : 0 < L x := by linarith
  have hK : K < D * L x := by
    have := (div_lt_iff₀ hD).mp hlK
    nlinarith only [this]
  let E01 := sieveBad ε x (a0 x) (b1 x) u0 v1 C01
  let E10 := sieveBad ε x (a1 x) (b0 x) u1 v0 C10
  let E11 := sieveBad ε x (a1 x) (b1 x) u1 v1 C11
  let Z := (Finset.Icc ⌈x⌉₊ ⌊x + x ^ (theta1 ε * theta2)⌋₊).filter
    (fun N => Even N ∧ Scount ε x N = 0)
  have hsub : Z ⊆ E01 ∪ E10 ∪ E11 := by
    intro N hN
    obtain ⟨hNK, hEven, hzero⟩ := Finset.mem_filter.mp hN
    by_contra hn
    have hn' : N ∉ E01 ∧ N ∉ E10 ∧ N ∉ E11 := by
      simpa only [Finset.mem_union, not_or, and_assoc] using hn
    have hg01 : |convIJ ε x (a0 x) (b1 x) N - u0 * v1 * sieveMain ε x N| ≤
        C01 * |u0 * v1 * sieveMain ε x N| / L x := by
      by_contra h
      exact hn'.1 (Finset.mem_filter.mpr ⟨hNK, hEven, lt_of_not_ge h⟩)
    have hg10 : |convIJ ε x (a1 x) (b0 x) N - u1 * v0 * sieveMain ε x N| ≤
        C10 * |u1 * v0 * sieveMain ε x N| / L x := by
      by_contra h
      exact hn'.2.1 (Finset.mem_filter.mpr ⟨hNK, hEven, lt_of_not_ge h⟩)
    have hg11 : |convIJ ε x (a1 x) (b1 x) N - u1 * v1 * sieveMain ε x N| ≤
        C11 * |u1 * v1 * sieveMain ε x N| / L x := by
      by_contra h
      exact hn'.2.2 (Finset.mem_filter.mpr ⟨hNK, hEven, lt_of_not_ge h⟩)
    have hpos := vector_main_positive (sieveMain_pos hε (by linarith) N) hl
      (mul_nonneg ha0.positive.le hb1.positive.le)
      (mul_nonneg ha1.positive.le hb0.positive.le)
      (mul_nonneg ha1.positive.le hb1.positive.le) hK hg01 hg10 hg11
    obtain ⟨hab, hbb⟩ := hXs x hxs
    have hv := vector_sieve_sum ε x primeIndicator (a0 x) (a1 x) (b0 x) (b1 x)
      (by intro k; unfold primeIndicator; split_ifs <;> norm_num)
      (fun k hk => (hab k hk).1) (fun k hk => (hab k hk).2)
      (fun m hm => (hbb m hm).1) (fun m hm => (hbb m hm).2) N
    rw [← Scount_eq_convIJ ε x N hxpos.le, hzero, Nat.cast_zero] at hv
    linarith
  have hcard : (Z.card : ℝ) ≤ (E01.card : ℝ) + (E10.card : ℝ) + (E11.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans
      ((Finset.card_union_le (E01 ∪ E10) E11).trans
        (Nat.add_le_add_right (Finset.card_union_le E01 E10) _))
  have htotal : (Z.card : ℝ) <
      3 * (x ^ (theta1 ε * theta2) / L x ^ (A + 1)) := by
    have := hX01 x hx01
    have := hX10 x hx10
    have := hX11 x hx11
    dsimp [E01, E10, E11] at hcard
    linarith
  have hsave : 3 * (x ^ (theta1 ε * theta2) / L x ^ (A + 1)) ≤
      x ^ (theta1 ε * theta2) / L x ^ A := by
    rw [Real.rpow_add hl, Real.rpow_one, div_mul_eq_div_div]
    calc 3 * (x ^ (theta1 ε * theta2) / L x ^ A / L x) =
        (x ^ (theta1 ε * theta2) / L x ^ A) * (3 / L x) := by ring
      _ ≤ (x ^ (theta1 ε * theta2) / L x ^ A) * 1 := by
        apply mul_le_mul_of_nonneg_left ((div_le_one hl).mpr hl3)
        positivity
      _ = _ := mul_one _
  exact htotal.trans_le hsave

/-- Theorem 1 conditional on Theorem 2 and the four sequence hypotheses only. -/
theorem theorem1_of_theorem2 {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 20000)
    (hT : Theorem2 ε)
    (a0 a1 b0 b1 : ℝ → ℕ → ℝ) (u0 u1 v0 v1 B : ℝ)
    (Ex0 Ex1 : ℝ → ∀ q : ℕ, Finset (DirichletCharacter ℂ q))
    (ha0 : ISequence ε a0 u0 B) (ha1 : ISequence ε a1 u1 B)
    (hb0 : JSequence ε b0 v0 B Ex0) (hb1 : JSequence ε b1 v1 B Ex1)
    (hsieve : VectorSieveBounds ε a0 a1 b0 b1)
    (hmargin : 0 < u0 * v1 + u1 * v0 - u1 * v1) : Theorem1 :=
  theorem1_of_prop12 hε hεsmall
    (prop12_of_theorem2 hε.le hT a0 a1 b0 b1 u0 u1 v0 v1 B Ex0 Ex1
      ha0 ha1 hb0 hb1 hsieve hmargin)

/-- The constants in equation 1.5 give a positive margin with positive upper densities. -/
theorem margin_of_15 {u0 u1 v0 v1 : ℝ} (hu0 : 0.99 < u0) (hu1 : u1 < 1.01)
    (hv0 : 0.05 < v0) (hv1 : v1 < 2.2) (hu1pos : 0 < u1) (hv1pos : 0 < v1) :
    0 < u0 * v1 + u1 * v0 - u1 * v1 := by
  rcases le_or_gt v0 v1 with hv | hv
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ u0 - 0.99) hv1pos.le,
      mul_nonneg (sub_nonneg.mpr hv) (by linarith : (0 : ℝ) ≤ 1.01 - u1)]
  · have hfirst : 0 < u0 * v1 := mul_pos (by linarith) hv1pos
    have hsecond : 0 < u1 * (v0 - v1) := mul_pos hu1pos (sub_pos.mpr hv)
    nlinarith only [hfirst, hsecond]

/-- Equation 1.2 using exactly the numerical bounds in equation 1.5. -/
theorem prop12_of_theorem2_15 {ε : ℝ} (hε : 0 ≤ ε) (hT : Theorem2 ε)
    (a0 a1 b0 b1 : ℝ → ℕ → ℝ) (u0 u1 v0 v1 B : ℝ)
    (Ex0 Ex1 : ℝ → ∀ q : ℕ, Finset (DirichletCharacter ℂ q))
    (ha0 : ISequence ε a0 u0 B) (ha1 : ISequence ε a1 u1 B)
    (hb0 : JSequence ε b0 v0 B Ex0) (hb1 : JSequence ε b1 v1 B Ex1)
    (hsieve : VectorSieveBounds ε a0 a1 b0 b1)
    (hu0 : 0.99 < u0) (hu1 : u1 < 1.01) (hv0 : 0.05 < v0) (hv1 : v1 < 2.2) : Prop12 ε :=
  prop12_of_theorem2 hε hT a0 a1 b0 b1 u0 u1 v0 v1 B Ex0 Ex1 ha0 ha1 hb0 hb1
    hsieve (margin_of_15 hu0 hu1 hv0 hv1 ha1.positive hb1.positive)

/-- Theorem 1 from Theorem 2, the four sequence hypotheses and equation 1.5. -/
theorem theorem1_of_theorem2_15 {ε : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 20000)
    (hT : Theorem2 ε)
    (a0 a1 b0 b1 : ℝ → ℕ → ℝ) (u0 u1 v0 v1 B : ℝ)
    (Ex0 Ex1 : ℝ → ∀ q : ℕ, Finset (DirichletCharacter ℂ q))
    (ha0 : ISequence ε a0 u0 B) (ha1 : ISequence ε a1 u1 B)
    (hb0 : JSequence ε b0 v0 B Ex0) (hb1 : JSequence ε b1 v1 B Ex1)
    (hsieve : VectorSieveBounds ε a0 a1 b0 b1)
    (hu0 : 0.99 < u0) (hu1 : u1 < 1.01) (hv0 : 0.05 < v0) (hv1 : v1 < 2.2) : Theorem1 :=
  theorem1_of_prop12 hε hεsmall
    (prop12_of_theorem2_15 hε.le hT a0 a1 b0 b1 u0 u1 v0 v1 B Ex0 Ex1 ha0 ha1 hb0 hb1
      hsieve hu0 hu1 hv0 hv1)

#print axioms Scount_eq_convIJ
#print axioms sieveBad_bound
#print axioms SS_pos
#print axioms sieveMain_pos
#print axioms vector_main_positive
#print axioms prop12_of_theorem2
#print axioms theorem1_of_theorem2
#print axioms margin_of_15
#print axioms prop12_of_theorem2_15
#print axioms theorem1_of_theorem2_15
end LeanLab.BakerHarmanPintz1997
