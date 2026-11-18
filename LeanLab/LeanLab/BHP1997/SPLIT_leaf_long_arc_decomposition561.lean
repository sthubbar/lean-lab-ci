/-
Independent split of the arc decomposition step of the long coefficient replacement.
The major arc integral is the integral over a finite family of Farey arcs; the four
inputs below supply the continuity of the integrand, the containment of every arc in the
complete period, the pairwise disjointness of the arcs and the additivity of the
integral over a finite disjoint union.  The assembly uses only those four inputs, plus
an elementary change of variable on a single arc.
AI wrote the Lean code.  Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_long_prefix_replacement561

namespace LeanLab.BHP1997.Decomp561n
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e Decomp561m

/-- LEAF. Continuity step.  The integrand is the product of the two finite polynomial
sums and one character of the circle, hence a finite sum of continuous functions of the
arc variable `t`, with no hypothesis on the coefficients and none on the parity of the
frequency.  This is what makes the integrand integrable on the bounded union of arcs
used in the union step. -/
theorem leaf561_integrand_continuous561 (ε x : ℝ) (a b : ℕ → ℂ) (N : ℕ) :
    Continuous (fun t : ℝ => integrand512 ε x a b N t) := by
  have hcoe : Continuous (fun t : ℝ => (t : AddCircle (1 : ℝ))) := AddCircle.continuous_mk' 1
  have hfour : ∀ n : ℤ, Continuous (fun t : ℝ => @fourier 1 n (t : AddCircle (1 : ℝ))) :=
    fun n => (fourier n).continuous.comp hcoe
  simp only [integrand512, polynomial512]
  exact Continuous.mul (Continuous.mul
    (continuous_finset_sum _ (fun k _ => continuous_const.mul (hfour _)))
    (continuous_finset_sum _ (fun k _ => continuous_const.mul (hfour _))))
    (hfour _)

/-- Elementary real algebra for the containment step: a centre `rr/qr` with `1 ≤ rr ≤ qr`,
a modulus at most half the Farey order and a small half width keep the arc inside the
complete period. -/
private theorem arc_algebra561 (rr qr Qr W Y t : ℝ) (hr1 : 1 ≤ rr) (hrq : rr ≤ qr)
    (hq1 : 1 ≤ qr) (h2q : 2 * qr ≤ Qr) (h4 : 4 * W ≤ Y) (hWQ : W * Qr ≤ Y)
    (hY : 0 < Y)
    (ht1 : rr / qr - W / (qr * Y) ≤ t) (ht2 : t ≤ rr / qr + W / (qr * Y)) :
    1 / Qr < t ∧ t ≤ 1 + 1 / Qr := by
  have hq0 : 0 < qr := by linarith
  have hQ0 : 0 < Qr := by linarith
  have hw1 : W / (qr * Y) ≤ 1 / (4 * qr) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h4 hq0.le]
  have hw2 : W / (qr * Y) ≤ 1 / Qr := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hq1 hY.le]
  have hl : 1 / Qr ≤ 1 / (2 * qr) := one_div_le_one_div_of_le (by positivity) h2q
  have ha : 1 / qr ≤ rr / qr := div_le_div_of_nonneg_right hr1 hq0.le
  have hb : rr / qr ≤ 1 := (div_le_one hq0).2 hrq
  have e1 : 1 / (2 * qr) = (1 / qr) / 2 := by rw [one_div, one_div, mul_inv]; ring
  have e2 : 1 / (4 * qr) = (1 / qr) / 4 := by rw [one_div, one_div, mul_inv]; ring
  have hp : 0 < 1 / qr := by positivity
  constructor <;> linarith

/-- LEAF. Containment step.  Every arc of the major arcs lies inside the complete
period of the circle.  The left end of the period is the reciprocal of the Farey order,
which eventually dominates the modulus cutoff, so the reduced centres sit at distance at
least `1/(M*(M+1))` above it while the half width of an arc is a logarithm power over
the block length; the right end is the same bound from below.  Only the elementary
growth of the order and the decay of the half width are used. -/
theorem leaf561_arcs_inside_period561 (ε D : ℝ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ q ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
      ∀ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        Set.Icc ((r : ℝ) / q - Real.log x ^ (4 * D) / (q * length512 ε x))
            ((r : ℝ) / q + Real.log x ^ (4 * D) / (q * length512 ε x)) ⊆
          period512 ε x := by
  by_cases hc : (11 / 20 + ε : ℝ) ≤ 0
  · refine ⟨1, fun x hx q hq => ?_⟩
    exfalso
    have hY : length512 ε x ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx hc
    have hY0 : 0 ≤ length512 ε x := Real.rpow_nonneg (by linarith) _
    have h1 : length512 ε x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ) ≤ 1 :=
      Real.rpow_le_one hY0 hY (by norm_num)
    have h2 : (length512 ε x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ (1 / 2 : ℝ) ≤ 1 :=
      Real.rpow_le_one (Real.rpow_nonneg hY0 _) h1 (by norm_num)
    have hQ : order512 ε x = 0 := by
      unfold order512
      rw [Nat.floor_eq_zero]
      linarith
    obtain ⟨a, b⟩ := Finset.mem_Icc.mp hq
    have := b.trans (min_le_left _ _)
    omega
  · have hc0 : (0 : ℝ) < 11 / 20 + ε := lt_of_not_ge hc
    have hp1 : (0 : ℝ) < (11 / 20 + ε) * (1 / 16 - 1 / 10 ^ 5) :=
      mul_pos hc0 (by norm_num)
    have hp2 : (0 : ℝ) < (11 / 20 + ε) * (1 - (1 / 16 - 1 / 10 ^ 5)) :=
      mul_pos hc0 (by norm_num)
    have eA := (isLittleO_log_rpow_rpow_atTop (2 * D) hp1).def
      (by norm_num : (0 : ℝ) < 1 / 8)
    have eB := (isLittleO_log_rpow_rpow_atTop (4 * D) hc0).def
      (by norm_num : (0 : ℝ) < 1 / 4)
    have eC := (isLittleO_log_rpow_rpow_atTop (4 * D) hp2).def
      (by norm_num : (0 : ℝ) < 1)
    have eE := (tendsto_rpow_atTop hp1).eventually_ge_atTop 4
    have e1 := Filter.eventually_ge_atTop (1 : ℝ)
    have hall : ∀ᶠ x : ℝ in Filter.atTop,
        ∀ q ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
        ∀ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          Set.Icc ((r : ℝ) / q - Real.log x ^ (4 * D) / (q * length512 ε x))
              ((r : ℝ) / q + Real.log x ^ (4 * D) / (q * length512 ε x)) ⊆
            period512 ε x := by
      filter_upwards [eA, eB, eC, eE, e1] with x hA hB hC hE hx1 q hq r hr
      have hx0 : (0 : ℝ) ≤ x := by linarith
      have hxp : (0 : ℝ) < x := by linarith
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 _)] at hA hB hC
      have hA' := (le_abs_self _).trans hA
      have hB' := (le_abs_self _).trans hB
      have hC' := (le_abs_self _).trans hC
      have hT : (length512 ε x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ (1 / 2 : ℝ) =
          x ^ ((11 / 20 + ε) * (1 / 16 - 1 / 10 ^ 5) : ℝ) := by
        unfold length512
        rw [← Real.rpow_mul hx0, ← Real.rpow_mul hx0]
        congr 1
        ring
      have hQ : order512 ε x = ⌊x ^ ((11 / 20 + ε) * (1 / 16 - 1 / 10 ^ 5) : ℝ) / 2⌋₊ := by
        unfold order512
        rw [hT]
      have hYdef : length512 ε x = x ^ (11 / 20 + ε : ℝ) := rfl
      have hYpos : 0 < length512 ε x := by rw [hYdef]; exact Real.rpow_pos_of_pos hxp _
      have hTpos : 0 < x ^ ((11 / 20 + ε) * (1 / 16 - 1 / 10 ^ 5) : ℝ) :=
        Real.rpow_pos_of_pos hxp _
      have hVT : x ^ ((11 / 20 + ε) * (1 - (1 / 16 - 1 / 10 ^ 5)) : ℝ) *
          x ^ ((11 / 20 + ε) * (1 / 16 - 1 / 10 ^ 5) : ℝ) = length512 ε x := by
        rw [hYdef, ← Real.rpow_add hxp]
        congr 1
        ring
      have hQle : (order512 ε x : ℝ) ≤ x ^ ((11 / 20 + ε) * (1 / 16 - 1 / 10 ^ 5) : ℝ) / 2 := by
        rw [hQ]; exact Nat.floor_le (by positivity)
      have hQlt : x ^ ((11 / 20 + ε) * (1 / 16 - 1 / 10 ^ 5) : ℝ) / 2 <
          (order512 ε x : ℝ) + 1 := by
        rw [hQ]; exact Nat.lt_floor_add_one _
      obtain ⟨hq1, hqm⟩ := Finset.mem_Icc.mp hq
      have hqP : (q : ℝ) ≤ Real.log x ^ (2 * D) :=
        (Nat.le_floor_iff' (by omega)).mp (hqm.trans (min_le_right _ _))
      obtain ⟨hrI, -⟩ := Finset.mem_filter.mp hr
      obtain ⟨hr1, hrq⟩ := Finset.mem_Icc.mp hrI
      have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
      have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
      have hrq' : (r : ℝ) ≤ q := by exact_mod_cast hrq
      have hW0 : 0 ≤ Real.log x ^ (4 * D) := Real.rpow_nonneg (Real.log_nonneg hx1) _
      have hV0 : 0 ≤ x ^ ((11 / 20 + ε) * (1 - (1 / 16 - 1 / 10 ^ 5)) : ℝ) :=
        Real.rpow_nonneg hx0 _
      have hWQ : Real.log x ^ (4 * D) * (order512 ε x : ℝ) ≤ length512 ε x := by
        have := mul_le_mul hC' hQle (Nat.cast_nonneg _) (by linarith)
        nlinarith
      intro t ht
      obtain ⟨ht1, ht2⟩ := ht
      unfold period512
      exact arc_algebra561 r q (order512 ε x) (Real.log x ^ (4 * D)) (length512 ε x) t
        hr1' hrq' hq1' (by linarith) (by rw [hYdef]; linarith) hWQ hYpos ht1 ht2
    obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hall
    exact ⟨X, hX⟩

/-- Standard fact: two different reduced fractions have different cross products. -/
private lemma farey_cross_ne561 (q₁ q₂ r₁ r₂ : ℕ) (hq₁ : 1 ≤ q₁)
    (h₁ : Nat.Coprime r₁ q₁) (h₂ : Nat.Coprime r₂ q₂) (hne : (q₁, r₁) ≠ (q₂, r₂)) :
    r₁ * q₂ ≠ r₂ * q₁ := by
  intro h
  have d₁ : q₁ ∣ q₂ := by
    apply Nat.Coprime.dvd_of_dvd_mul_left h₁.symm
    rw [h]
    exact Dvd.intro_left _ rfl
  have d₂ : q₂ ∣ q₁ := by
    apply Nat.Coprime.dvd_of_dvd_mul_left h₂.symm
    rw [← h]
    exact Dvd.intro_left _ rfl
  have hqq : q₁ = q₂ := Nat.dvd_antisymm d₁ d₂
  subst hqq
  have hrr : r₁ = r₂ := Nat.eq_of_mul_eq_mul_right (by omega) h
  exact hne (by rw [hrr])

/-- Farey separation: cross products differing by at least one put the centres at least
`1/(q₁ q₂)` apart, which exceeds the sum of the two half widths. -/
private lemma arc_half_sep561 (q₁ q₂ r₁ r₂ : ℕ) (hq₁ : 1 ≤ q₁) (hq₂ : 1 ≤ q₂)
    (hlt : r₁ * q₂ + 1 ≤ r₂ * q₁) (L4 L2 Y : ℝ) (hL4 : 0 ≤ L4)
    (hq₁L : (q₁ : ℝ) ≤ L2) (hq₂L : (q₂ : ℝ) ≤ L2) (hY : 0 < Y)
    (hsmall : 2 * L4 * L2 < Y)
    (h : (r₂ : ℝ) / q₂ - L4 / (q₂ * Y) ≤ (r₁ : ℝ) / q₁ + L4 / (q₁ * Y)) : False := by
  have p₁ : (0 : ℝ) < q₁ := by exact_mod_cast hq₁
  have p₂ : (0 : ℝ) < q₂ := by exact_mod_cast hq₂
  have hP : (0 : ℝ) < q₁ * q₂ * Y := by positivity
  have hm := mul_le_mul_of_nonneg_right h hP.le
  have e₁ : ((r₂ : ℝ) / q₂ - L4 / (q₂ * Y)) * (q₁ * q₂ * Y) = r₂ * q₁ * Y - L4 * q₁ := by
    field_simp
  have e₂ : ((r₁ : ℝ) / q₁ + L4 / (q₁ * Y)) * (q₁ * q₂ * Y) = r₁ * q₂ * Y + L4 * q₂ := by
    field_simp
  rw [e₁, e₂] at hm
  have hc : (r₁ : ℝ) * q₂ + 1 ≤ r₂ * q₁ := by exact_mod_cast hlt
  have hcY := mul_le_mul_of_nonneg_right hc hY.le
  have b₁ := mul_le_mul_of_nonneg_left hq₁L hL4
  have b₂ := mul_le_mul_of_nonneg_left hq₂L hL4
  nlinarith

/-- LEAF. Separation step.  Two distinct arcs are disjoint.  Two different reduced
fractions with moduli at most the Farey order differ by at least the reciprocal of the
product of their moduli, while twice the half width of an arc is a logarithm power over
the block length, which is smaller than that reciprocal from some point on.  Reducedness
is what makes the two centres different rationals. -/
theorem leaf561_arcs_pairwise_disjoint561 (ε D : ℝ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ q₁ ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
      ∀ r₁ ∈ (Finset.Icc 1 q₁).filter (fun r => Nat.Coprime r q₁),
      ∀ q₂ ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
      ∀ r₂ ∈ (Finset.Icc 1 q₂).filter (fun r => Nat.Coprime r q₂),
        (q₁, r₁) ≠ (q₂, r₂) →
          Disjoint
            (Set.Icc ((r₁ : ℝ) / q₁ - Real.log x ^ (4 * D) / (q₁ * length512 ε x))
              ((r₁ : ℝ) / q₁ + Real.log x ^ (4 * D) / (q₁ * length512 ε x)))
            (Set.Icc ((r₂ : ℝ) / q₂ - Real.log x ^ (4 * D) / (q₂ * length512 ε x))
              ((r₂ : ℝ) / q₂ + Real.log x ^ (4 * D) / (q₂ * length512 ε x))) := by
  by_cases hc : 11 / 20 + ε ≤ 0
  · refine ⟨1, fun x hx q₁ hq₁ => ?_⟩
    exfalso
    have hY1 : length512 ε x ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx hc
    have hY0 : 0 ≤ length512 ε x := Real.rpow_nonneg (by linarith) _
    have hA : length512 ε x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ) ≤ 1 :=
      Real.rpow_le_one hY0 hY1 (by norm_num)
    have hA0 : 0 ≤ length512 ε x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ) := Real.rpow_nonneg hY0 _
    have hB : (length512 ε x ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ (1 / 2 : ℝ) ≤ 1 :=
      Real.rpow_le_one hA0 hA (by norm_num)
    have hQ : order512 ε x = 0 := by
      unfold order512
      rw [Nat.floor_eq_zero]
      linarith
    have h := (Finset.mem_Icc.mp hq₁)
    have h2 := le_trans h.2 (min_le_left _ _)
    rw [hQ] at h2
    omega
  · have hcpos : 0 < 11 / 20 + ε := lt_of_not_ge hc
    have hlo := (isLittleO_log_rpow_rpow_atTop (4 * D + 2 * D) hcpos).def
      (show (0 : ℝ) < 1 / 4 by norm_num)
    obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp hlo
    refine ⟨max 2 X₀, fun x hx q₁ hq₁ r₁ hr₁ q₂ hq₂ r₂ hr₂ hne => ?_⟩
    have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
    have hxX : X₀ ≤ x := le_trans (le_max_right _ _) hx
    have hlog : 0 < Real.log x := Real.log_pos (by linarith)
    have hYpos : 0 < length512 ε x := Real.rpow_pos_of_pos (by linarith) _
    have hYeq : length512 ε x = x ^ (11 / 20 + ε) := rfl
    have hL4 : 0 ≤ Real.log x ^ (4 * D) := Real.rpow_nonneg hlog.le _
    have hL2 : 0 ≤ Real.log x ^ (2 * D) := Real.rpow_nonneg hlog.le _
    have hs := hX₀ x hxX
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_add hlog, ← hYeq,
      abs_of_nonneg (mul_nonneg hL4 hL2), abs_of_pos hYpos] at hs
    have hsmall : 2 * Real.log x ^ (4 * D) * Real.log x ^ (2 * D) < length512 ε x := by
      nlinarith
    have hq₁' := Finset.mem_Icc.mp hq₁
    have hq₂' := Finset.mem_Icc.mp hq₂
    have hr₁' := (Finset.mem_filter.mp hr₁).2
    have hr₂' := (Finset.mem_filter.mp hr₂).2
    have hq₁L : (q₁ : ℝ) ≤ Real.log x ^ (2 * D) :=
      le_trans (Nat.cast_le.mpr (le_trans hq₁'.2 (min_le_right _ _))) (Nat.floor_le hL2)
    have hq₂L : (q₂ : ℝ) ≤ Real.log x ^ (2 * D) :=
      le_trans (Nat.cast_le.mpr (le_trans hq₂'.2 (min_le_right _ _))) (Nat.floor_le hL2)
    have hcross := farey_cross_ne561 q₁ q₂ r₁ r₂ hq₁'.1 hr₁' hr₂' hne
    rw [Set.disjoint_left]
    intro t ht₁ ht₂
    rcases Nat.lt_or_gt_of_ne hcross with hlt | hgt
    · exact arc_half_sep561 q₁ q₂ r₁ r₂ hq₁'.1 hq₂'.1 hlt _ _ _ hL4 hq₁L hq₂L hYpos hsmall
        (le_trans ht₂.1 ht₁.2)
    · exact arc_half_sep561 q₂ q₁ r₂ r₁ hq₂'.1 hq₁'.1 hgt _ _ _ hL4 hq₂L hq₁L hYpos hsmall
        (le_trans ht₁.1 ht₂.2)

/-- LEAF. Union additivity step.  For a continuous integrand and a two level family of
closed arcs that is pairwise disjoint, the integral over the union is the iterated sum of
the integrals over the single arcs.  This is the only measure theoretic step: the arcs
are measurable, their union is a finite one, and continuity makes the integrand
integrable on each arc and on the union.  No arithmetic and no distribution hypothesis
is used. -/
theorem leaf561_union_integral561 (f : ℝ → ℂ) (hf : Continuous f)
    (S : Finset ℕ) (T : ℕ → Finset ℕ) (c w : ℕ → ℕ → ℝ)
    (hdisj : ∀ q₁ ∈ S, ∀ r₁ ∈ T q₁, ∀ q₂ ∈ S, ∀ r₂ ∈ T q₂, (q₁, r₁) ≠ (q₂, r₂) →
      Disjoint (Set.Icc (c q₁ r₁ - w q₁ r₁) (c q₁ r₁ + w q₁ r₁))
        (Set.Icc (c q₂ r₂ - w q₂ r₂) (c q₂ r₂ + w q₂ r₂))) :
    (∫ t in (⋃ q ∈ S, ⋃ r ∈ T q, Set.Icc (c q r - w q r) (c q r + w q r)), f t) =
      ∑ q ∈ S, ∑ r ∈ T q, ∫ t in Set.Icc (c q r - w q r) (c q r + w q r), f t := by
  have hint : ∀ q r, IntegrableOn f (Set.Icc (c q r - w q r) (c q r + w q r)) volume :=
    fun q r => hf.continuousOn.integrableOn_Icc
  have hinner : ∀ q ∈ S,
      (∫ t in (⋃ r ∈ T q, Set.Icc (c q r - w q r) (c q r + w q r)), f t) =
        ∑ r ∈ T q, ∫ t in Set.Icc (c q r - w q r) (c q r + w q r), f t := by
    intro q hq
    refine MeasureTheory.integral_biUnion_finset (T q) (fun r _ => measurableSet_Icc) ?_
      (fun r _ => hint q r)
    intro r₁ hr₁ r₂ hr₂ hne
    exact hdisj q hq r₁ hr₁ q hq r₂ hr₂ (fun h => hne (Prod.mk.inj h).2)
  have houter :
      (∫ t in (⋃ q ∈ S, ⋃ r ∈ T q, Set.Icc (c q r - w q r) (c q r + w q r)), f t) =
        ∑ q ∈ S, ∫ t in (⋃ r ∈ T q, Set.Icc (c q r - w q r) (c q r + w q r)), f t := by
    refine MeasureTheory.integral_biUnion_finset S
      (s := fun q => ⋃ r ∈ T q, Set.Icc (c q r - w q r) (c q r + w q r))
      (fun q _ => Finset.measurableSet_biUnion _ (fun r _ => measurableSet_Icc)) ?_ ?_
    · intro q₁ hq₁ q₂ hq₂ hne
      show Disjoint (⋃ r ∈ T q₁, Set.Icc (c q₁ r - w q₁ r) (c q₁ r + w q₁ r))
        (⋃ r ∈ T q₂, Set.Icc (c q₂ r - w q₂ r) (c q₂ r + w q₂ r))
      rw [Set.disjoint_left]
      intro t h1 h2
      simp only [Set.mem_iUnion] at h1 h2
      obtain ⟨r₁, hr₁, h1⟩ := h1
      obtain ⟨r₂, hr₂, h2⟩ := h2
      exact Set.disjoint_left.mp
        (hdisj q₁ hq₁ r₁ hr₁ q₂ hq₂ r₂ hr₂ (fun h => hne (Prod.mk.inj h).1)) h1 h2
    · intro q _
      exact (MeasureTheory.integrableOn_finset_iUnion).mpr (fun r _ => hint q r)
  rw [houter]
  exact Finset.sum_congr rfl hinner

/-- A single arc: the set integral over the closed interval equals the integral in the
local variable of the arc, with the centre moved into the integrand. -/
private theorem arc_translate561 (f : ℝ → ℂ) (c w : ℝ) (hw : 0 ≤ w) :
    ∫ t in Set.Icc (c - w) (c + w), f t = ∫ s in (-w)..w, f (c + s) := by
  have hle : c - w ≤ c + w := by linarith
  have h1 : ∫ t in Set.Icc (c - w) (c + w), f t = ∫ t in (c - w)..(c + w), f t := by
    rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Icc_eq_integral_Ioc]
  have h2 : ∫ t in (c - w)..(c + w), f t = ∫ t in (-w)..w, f (t + c) := by
    rw [intervalIntegral.integral_comp_add_right (f := f) (a := -w) (b := w) (d := c)]
    rw [show -w + c = c - w by ring, show w + c = c + w by ring]
  have h3 : ∫ t in (-w)..w, f (t + c) = ∫ s in (-w)..w, f (c + s) := by
    apply intervalIntegral.integral_congr
    intro s _
    exact congrArg f (add_comm s c)
  rw [h1, h2, h3]

/-- The single frequency arc decomposition, assembled from the continuity of the
integrand, the containment of the arcs in the complete period, their pairwise
disjointness and the additivity of the integral over a finite disjoint union.
CONDITIONAL ON those four separate inputs. -/
theorem leaf_long_arc_decomposition561_split (ε D : ℝ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ (a b : ℝ → ℕ → ℂ) (N : ℕ),
      (∫ t in major512 ε D x, integrand512 ε x (a x) (b x) N t) =
        ∑ q ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
          ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
            ∫ s in (-(Real.log x ^ (4 * D) / (q * length512 ε x)))..
                (Real.log x ^ (4 * D) / (q * length512 ε x)),
              integrand512 ε x (a x) (b x) N ((r : ℝ) / q + s) := by
  obtain ⟨Xc, hXc⟩ := leaf561_arcs_inside_period561 ε D
  obtain ⟨Xd, hXd⟩ := leaf561_arcs_pairwise_disjoint561 ε D
  refine ⟨max (max Xc Xd) 1 + 1, ?_⟩
  intro x hx a b N
  have hbig : (max (max Xc Xd) 1 : ℝ) ≤ x := by linarith
  have hone : (1 : ℝ) ≤ max (max Xc Xd) 1 := le_max_right _ _
  have hx1 : (1 : ℝ) ≤ x := le_trans hone hbig
  have hxm : max Xc Xd ≤ x := le_trans (le_max_left (max Xc Xd) (1 : ℝ)) hbig
  have hxc : Xc ≤ x := le_trans (le_max_left Xc Xd) hxm
  have hxd : Xd ≤ x := le_trans (le_max_right Xc Xd) hxm
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < length512 ε x := Real.rpow_pos_of_pos hxpos _
  have hWnn : ∀ q : ℕ, 1 ≤ q → 0 ≤ Real.log x ^ (4 * D) / (q * length512 ε x) := by
    intro q hq
    apply div_nonneg (Real.rpow_nonneg (le_of_lt hlog) _)
    exact mul_nonneg (Nat.cast_nonneg q) (le_of_lt hLpos)
  have hsub : (⋃ q ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
        ⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          Set.Icc ((r : ℝ) / q - Real.log x ^ (4 * D) / (q * length512 ε x))
            ((r : ℝ) / q + Real.log x ^ (4 * D) / (q * length512 ε x))) ⊆
      period512 ε x := by
    intro t ht
    simp only [Set.mem_iUnion] at ht
    obtain ⟨q, hq, r, hr, ht⟩ := ht
    exact hXc x hxc q hq r hr ht
  have hunion : major512 ε D x =
      ⋃ q ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
        ⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          Set.Icc ((r : ℝ) / q - Real.log x ^ (4 * D) / (q * length512 ε x))
            ((r : ℝ) / q + Real.log x ^ (4 * D) / (q * length512 ε x)) := by
    have hmaj : major512 ε D x =
        period512 ε x ∩
          ⋃ q ∈ Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊),
            ⋃ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
              Set.Icc ((r : ℝ) / q - Real.log x ^ (4 * D) / (q * length512 ε x))
                ((r : ℝ) / q + Real.log x ^ (4 * D) / (q * length512 ε x)) := rfl
    rw [hmaj]
    ext t
    constructor
    · rintro ⟨-, ht⟩
      exact ht
    · intro ht
      exact ⟨hsub ht, ht⟩
  rw [hunion]
  rw [leaf561_union_integral561 (fun t : ℝ => integrand512 ε x (a x) (b x) N t)
    (leaf561_integrand_continuous561 ε x (a x) (b x) N)
    (Finset.Icc 1 (min (order512 ε x) ⌊Real.log x ^ (2 * D)⌋₊))
    (fun q => (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q))
    (fun q r => (r : ℝ) / q)
    (fun q r => Real.log x ^ (4 * D) / (q * length512 ε x))
    (hXd x hxd)]
  refine Finset.sum_congr rfl (fun q hq => Finset.sum_congr rfl (fun r hr => ?_))
  exact arc_translate561 (fun t : ℝ => integrand512 ε x (a x) (b x) N t)
    ((r : ℝ) / q) (Real.log x ^ (4 * D) / (q * length512 ε x))
    (hWnn q (Finset.mem_Icc.mp hq).1)

end LeanLab.BHP1997.Decomp561n
