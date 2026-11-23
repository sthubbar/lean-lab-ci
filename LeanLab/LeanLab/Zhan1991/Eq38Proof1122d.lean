/-
P0068 Zhan 1991, page 265, displays (3.9) and (3.10): the step from (3.11) and (3.12) to (3.8).
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Route: the weight `wt38` is at most `A`, at most `2N/|t + 2πλN|` once that is at least
`H = N/A` because `4π|λ|A ≤ H`, and at most `2N/|t|` once `|t| ≥ T₀`. The range `|t| ≤ T₀` is
cut into intervals of length `H` on both sides of `-2πλN`, with weight `2A/m` on the `m`-th,
and the harmonic sum is `≪ L`; the range `T₀ < |t| ≤ T` is cut dyadically, `≪ L` pieces each
bounded by (3.12). Both inputs are used with `c₀ + 1` to absorb the factor `L`.
-/
import LeanLab.Zhan1991.SPLIT_theorem2_1122

namespace LeanLab.Zhan1991
open Finset Real MeasureTheory

noncomputable section

/-- The weight of (3.8) is nonnegative. -/
theorem wt38_nonneg' (N : ℕ) (A lam t : ℝ) (hA : 0 ≤ A) : 0 ≤ wt38 N A lam t := by
  unfold wt38
  simp only
  have hm : 0 ≤ sInf ((fun u => |t + 2 * π * lam * u|) '' Set.Icc ((N : ℝ) - A) N) :=
    Real.sInf_nonneg (by rintro _ ⟨u, _, rfl⟩; exact abs_nonneg _)
  split_ifs
  · exact hA
  · exact le_min hA (div_nonneg (Nat.cast_nonneg _) hm)

/-- The weight of (3.8) is at most `A`. -/
theorem wt38_le_A (N : ℕ) (A lam t : ℝ) : wt38 N A lam t ≤ A := by
  unfold wt38
  simp only
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- If `|t + 2πλu| ≥ μ > 0` on `[N - A, N]` then the weight of (3.8) is at most `N/μ`. -/
theorem wt38_le_of (N : ℕ) (A lam t μ : ℝ) (hA : 0 ≤ A) (hμ : 0 < μ)
    (h : ∀ u ∈ Set.Icc ((N : ℝ) - A) N, μ ≤ |t + 2 * π * lam * u|) :
    wt38 N A lam t ≤ N / μ := by
  unfold wt38
  simp only
  have hne : (Set.Icc ((N : ℝ) - A) N).Nonempty := ⟨N, by constructor <;> linarith⟩
  have hm : μ ≤ sInf ((fun u => |t + 2 * π * lam * u|) '' Set.Icc ((N : ℝ) - A) N) :=
    le_csInf (hne.image _) (by rintro _ ⟨u, hu, rfl⟩; exact h u hu)
  rw [if_neg (by linarith)]
  exact (min_le_right _ _).trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hμ hm)

/-- `F(1/2 + it, χ)` of display (3.6) is continuous in `t`. -/
theorem Fprod_continuous {q : ℕ} (Nv : Fin 20 → ℝ) (χ : DirichletCharacter ℂ q) :
    Continuous (fun t : ℝ => Fprod Nv χ (1 / 2 + t * Complex.I)) := by
  unfold Fprod fj
  apply continuous_finsetProd
  intro j _
  apply continuous_finsetSum
  intro n hn
  have hn1 : 1 ≤ n := by
    simp only [dyad, Finset.mem_filter, Finset.mem_Icc] at hn
    exact hn.1.1
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  exact continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hn0))

/-- A finite covering bound: if `w ≤ Σ cᵢ 1_{Iᵢ}` on `[a, b]`, then
`∫_a^b w f ≤ Σ cᵢ ∫_{Iᵢ} f` for nonnegative `w`, `f` with `f` integrable on each `Iᵢ`. -/
theorem integral_le_pieces {ι : Type*} (s : Finset ι) (I : ι → Set ℝ) (c : ι → ℝ)
    (w f : ℝ → ℝ) (a b : ℝ) (hI : ∀ i, MeasurableSet (I i))
    (hfI : ∀ i ∈ s, IntegrableOn f (I i)) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hw : ∀ t, 0 ≤ w t) (hf : ∀ t, 0 ≤ f t)
    (hcov : ∀ t ∈ Set.Icc a b, w t ≤ ∑ i ∈ s, (I i).indicator (fun _ => c i) t) :
    ∫ t in Set.Icc a b, w t * f t ≤ ∑ i ∈ s, c i * ∫ t in I i, f t := by
  set G : ℝ → ℝ := fun t => ∑ i ∈ s, (I i).indicator (fun t => c i * f t) t with hG
  have hGi : Integrable G := by
    apply integrable_finsetSum
    intro i hi
    exact (integrable_indicator_iff (hI i)).2 ((hfI i hi).const_mul (c i))
  have hG0 : ∀ t, 0 ≤ G t := by
    intro t
    apply Finset.sum_nonneg
    intro i hi
    exact Set.indicator_nonneg (fun t _ => mul_nonneg (hc i hi) (hf t)) t
  have h1 : ∫ t in Set.Icc a b, w t * f t ≤ ∫ t in Set.Icc a b, G t := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun t => mul_nonneg (hw t) (hf t))
    · exact hGi.integrableOn
    · refine ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => ?_)
      have := mul_le_mul_of_nonneg_right (hcov t ht) (hf t)
      refine this.trans (le_of_eq ?_)
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hti : t ∈ I i
      · simp [Set.indicator_of_mem hti]
      · simp [Set.indicator_of_notMem hti]
  have h2 : ∫ t in Set.Icc a b, G t ≤ ∫ t, G t :=
    setIntegral_le_integral hGi (Filter.Eventually.of_forall hG0)
  have h3 : ∫ t, G t = ∑ i ∈ s, c i * ∫ t in I i, f t := by
    rw [hG, integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_indicator (hI i), integral_const_mul]
    · intro i hi
      exact (integrable_indicator_iff (hI i)).2 ((hfI i hi).const_mul (c i))
  linarith

/-- The harmonic sum with the `m = 0` term read as `1`: `Σ_{m ≤ R} 1/max(1, m) ≤ 2 + log R`. -/
theorem sum_inv_max_le (R : ℕ) :
    ∑ m ∈ Finset.range (R + 1), 1 / max 1 (m : ℝ) ≤ 2 + Real.log R := by
  rw [Finset.sum_range_succ']
  have hh := harmonic_le_one_add_log R
  have hcast : ((harmonic R : ℚ) : ℝ) = ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1) := by
    simp [harmonic, Rat.cast_sum]
  have heq : ∑ i ∈ Finset.range R, 1 / max 1 (((i + 1 : ℕ) : ℝ)) =
      ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [max_eq_right (by push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])]
    push_cast; ring
  rw [heq, ← hcast]
  simp only [Nat.cast_zero, max_eq_left (zero_le_one' ℝ), div_one]
  linarith

/-- Dyadic location: every `x > 1` has `2^j < x ≤ 2^{j+1}` for some `j`. -/
theorem exists_two_pow_between (x : ℝ) (hx : 1 < x) :
    ∃ j : ℕ, (2 : ℝ) ^ j < x ∧ x ≤ 2 ^ (j + 1) := by
  classical
  have hex : ∃ n : ℕ, x ≤ (2 : ℝ) ^ n := (pow_unbounded_of_one_lt x (by norm_num : (1:ℝ) < 2)).imp fun _ h => h.le
  obtain ⟨n, hn⟩ : ∃ n, n = Nat.find hex := ⟨_, rfl⟩
  have hspec : x ≤ (2 : ℝ) ^ n := hn ▸ Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, pow_zero] at hspec
    linarith
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  refine ⟨j, ?_, hspec⟩
  by_contra hcon
  push_neg at hcon
  have := Nat.find_min hex (show j < Nat.find hex by omega)
  exact this hcon

set_option maxHeartbeats 2000000 in
/-- Page 265, displays (3.9) and (3.10): (3.11) and (3.12) give (3.8). The range `|t| ≤ T₀` is
cut into the intervals `(s₀ + mH, s₀ + (m+1)H]` and `(s₀ - (m+1)H, s₀ - mH]`, `s₀ = -2πλN`,
`H = N/A`, with weight `2A/m`; the range `T₀ < |t| ≤ T` into `±(T₀2^j, T₀2^{j+1}]` with weight
`2N/(T₀2^j)`. Both inputs are used with `c₀ + 1`. -/
theorem eq38_of_eq311_eq312_proof (h311 : Eq311) (h312 : Eq312) : Eq38 := by
  intro B hB c0 hc0 ε hε
  obtain ⟨c1a, hc1a⟩ := h311 B hB (c0 + 1) (by linarith)
  obtain ⟨c1b, hc1b⟩ := h312 B hB (c0 + 1) (by linarith) ε hε
  refine ⟨max (max c1a c1b) 0, fun c1 hc1 => ?_⟩
  have hc1a' : c1a ≤ c1 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hc1
  have hc1b' : c1b ≤ c1 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hc1
  have hc10 : 0 ≤ c1 := le_trans (le_max_right _ _) hc1
  obtain ⟨c2a, hc2a⟩ := hc1a c1 hc1a'
  obtain ⟨c2b, hc2b⟩ := hc1b c1 hc1b'
  refine ⟨max (max c2a c2b) (c1 + 1), fun c2 hc2 => ?_⟩
  have hc2a' : c2a ≤ c2 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hc2
  have hc2b' : c2b ≤ c2 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hc2
  have hc21 : c1 + 1 ≤ c2 := le_trans (le_max_right _ _) hc2
  obtain ⟨c3a, hc3a, K1, N1, H1⟩ := hc2a c2 hc2a'
  obtain ⟨c3b, hc3b, K2, N2, H2⟩ := hc2b c2 hc2b'
  refine ⟨max c3a c3b, lt_max_of_lt_left hc3a,
    12 * max K1 0 + 4 * (3 + 4 * ε) * max K2 0, max (max N1 N2) (Real.exp 20), ?_⟩
  intro N A lam q _ Nv hN hyp hc
  have hNa : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNe : Real.exp 20 ≤ N := le_trans (le_max_right _ _) hN
  have Npos : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hNe
  have hexp : (21 : ℝ) ≤ Real.exp 20 := by linarith [Real.add_one_le_exp (20 : ℝ)]
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNbig : (21 : ℝ) ≤ N := by linarith
  have hL20 : 20 ≤ Real.log N := (Real.le_log_iff_exp_le Npos).2 hNe
  set L := Real.log N with hLdef
  have Lpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  obtain ⟨hA1, hA2, hq1, hq2, hq3, hlam⟩ := hyp
  have hc3mono : ∀ c3' ≤ max c3a c3b, (N : ℝ) ^ (3 / 5 : ℝ) * L ^ c3' ≤ A := fun c3' h =>
    le_trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 h)
      (Real.rpow_nonneg Npos.le _)) hA1
  have hypa : Hyp2 c1 c2 c3a N A lam q :=
    ⟨hc3mono _ (le_max_left _ _), hA2, hq1, hq2, hq3, hlam⟩
  have hypb : Hyp2 c1 c2 c3b N A lam q :=
    ⟨hc3mono _ (le_max_right _ _), hA2, hq1, hq2, hq3, hlam⟩
  have hA1' : 1 ≤ A := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (3 / 5 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
    have h2 : (1 : ℝ) ≤ L ^ (max c3a c3b) := Real.one_le_rpow hL1 (le_max_of_le_left hc3a.le)
    nlinarith
  have Apos : 0 < A := by linarith
  have hAN : A ≤ N := by
    have := Real.rpow_le_rpow_of_exponent_le hN1 (show (2 / 3 : ℝ) ≤ 1 by norm_num)
    rw [Real.rpow_one] at this
    linarith
  have hq1r : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  set H := (N : ℝ) / A with hHdef
  have Hpos : 0 < H := div_pos Npos Apos
  have hHN : H ≤ N := div_le_self Npos.le hA1'
  have hpi4 : π ≤ 4 := Real.pi_le_four
  have hpi3 : 3 < π := Real.pi_gt_three
  -- `4π|λ|A ≤ H`, from `|λ| ≤ 1/(qτ)`, `q ≥ L^{c₂}`, `c₂ ≥ c₁ + 1` and `L ≥ 4π`
  have hlamb : 4 * π * |lam| * A ≤ H := by
    have hτpos : 0 < A ^ 2 / N * L := by positivity
    have hLc : L ≤ L ^ c2 * L ^ (-c1) := by
      rw [← Real.rpow_add Lpos]
      calc L = L ^ (1 : ℝ) := (Real.rpow_one L).symm
        _ ≤ L ^ (c2 + -c1) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have hX : A ^ 2 / N * L ≤ q * (A ^ 2 / N * L ^ (-c1)) := by
      calc A ^ 2 / N * L ≤ A ^ 2 / N * (L ^ c2 * L ^ (-c1)) :=
            mul_le_mul_of_nonneg_left hLc (by positivity)
        _ = L ^ c2 * (A ^ 2 / N * L ^ (-c1)) := by ring
        _ ≤ q * (A ^ 2 / N * L ^ (-c1)) :=
            mul_le_mul_of_nonneg_right hq2 (by positivity)
    have hl : |lam| ≤ 1 / (A ^ 2 / N * L) := hlam.trans (one_div_le_one_div_of_le hτpos hX)
    have e : 4 * π * (1 / (A ^ 2 / N * L)) * A = (4 * π / L) * H := by
      rw [hHdef]; field_simp
    have h4 : 4 * π / L ≤ 1 := by rw [div_le_one Lpos]; linarith
    calc 4 * π * |lam| * A ≤ 4 * π * (1 / (A ^ 2 / N * L)) * A := by gcongr
      _ = (4 * π / L) * H := e
      _ ≤ 1 * H := mul_le_mul_of_nonneg_right h4 Hpos.le
      _ = H := one_mul H
  set s0 : ℝ := -2 * π * lam * N with hs0def
  set T0 := T0cut N A lam with hT0def
  set T := Tcut q N A lam ε with hTdef
  have hT0 : T0 = 4 * π * (|lam| * N + H) := rfl
  have hlN : 0 ≤ |lam| * N := by positivity
  have hs0 : |s0| = 2 * π * |lam| * N := by
    rw [hs0def, show -2 * π * lam * (N : ℝ) = -(2 * π * N * lam) by ring, abs_neg, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * π * N)]
    ring
  have hpH : 0 ≤ π * H := by positivity
  have hs0T : |s0| ≤ T0 / 2 := by rw [hs0]; linarith [hT0, hpH]
  have hHT0 : 4 * H ≤ T0 := by
    nlinarith [hT0, mul_pos (show (0 : ℝ) < π - 1 by linarith) Hpos,
      mul_nonneg Real.pi_pos.le hlN]
  have T0pos : 0 < T0 := by linarith
  have hs0b := abs_le.1 hs0T
  -- pointwise bounds for the weight
  have hw0 : ∀ t, 0 ≤ wt38 N A lam t := fun t => wt38_nonneg' N A lam t Apos.le
  have hwA : ∀ t, wt38 N A lam t ≤ A := fun t => wt38_le_A N A lam t
  have hwfar : ∀ t, H ≤ |t - s0| → wt38 N A lam t ≤ 2 * N / |t - s0| := by
    intro t ht
    have hpos : 0 < |t - s0| / 2 := by linarith
    have hb0 := wt38_le_of N A lam t (|t - s0| / 2) Apos.le hpos (by
      intro u hu
      have hu1 : |u - N| ≤ A := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
      have hb : |2 * π * lam * (u - N)| ≤ H / 2 := by
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
        have := mul_le_mul_of_nonneg_left hu1 (by positivity : (0 : ℝ) ≤ 2 * π * |lam|)
        linarith
      have he : t + 2 * π * lam * u = (t - s0) - (-(2 * π * lam * (u - N))) := by
        rw [hs0def]; ring
      rw [he]
      have := abs_sub_abs_le_abs_sub (t - s0) (-(2 * π * lam * (u - N)))
      rw [abs_neg] at this
      linarith)
    calc wt38 N A lam t ≤ N / (|t - s0| / 2) := hb0
      _ = 2 * N / |t - s0| := by rw [div_div_eq_mul_div]; ring
  have hwbig : ∀ t, T0 ≤ |t| → wt38 N A lam t ≤ 2 * N / |t| := by
    intro t ht
    have hpos : 0 < |t| / 2 := by linarith
    have hb0 := wt38_le_of N A lam t (|t| / 2) Apos.le hpos (by
      intro u hu
      have hu0 : 0 ≤ u := by linarith [hu.1]
      have hu1 : |u| ≤ N := by rw [abs_of_nonneg hu0]; exact hu.2
      have hb : |2 * π * lam * u| ≤ T0 / 2 := by
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
        have := mul_le_mul_of_nonneg_left hu1 (by positivity : (0 : ℝ) ≤ 2 * π * |lam|)
        linarith [hT0, hpH]
      have := abs_sub_abs_le_abs_sub t (-(2 * π * lam * u))
      rw [abs_neg, sub_neg_eq_add] at this
      linarith)
    calc wt38 N A lam t ≤ N / (|t| / 2) := hb0
      _ = 2 * N / |t| := by rw [div_div_eq_mul_div]; ring
  have hwm : ∀ (m : ℕ) (t : ℝ), (m : ℝ) * H ≤ |t - s0| →
      wt38 N A lam t ≤ 2 * A / max 1 (m : ℝ) := by
    intro m t ht
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [Nat.cast_zero, max_eq_left zero_le_one, div_one]
      linarith [hwA t]
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      rw [max_eq_right hm1]
      have hH : H ≤ |t - s0| := le_trans (by nlinarith) ht
      have hpos : 0 < (m : ℝ) * H := by positivity
      calc wt38 N A lam t ≤ 2 * N / |t - s0| := hwfar t hH
        _ ≤ 2 * N / ((m : ℝ) * H) := div_le_div_of_nonneg_left (by positivity) hpos ht
        _ = 2 * A / m := by rw [hHdef]; field_simp
  -- the pieces
  set R := ⌈2 * T0 / H⌉₊ + 1 with hRdef
  set M := ⌊2 * (1 + 2 * ε) * L⌋₊ + 1 with hMdef
  let T1p : ℕ → ℝ := fun m => s0 + m * H
  let T1n : ℕ → ℝ := fun m => s0 - (m + 1) * H
  let T2p : ℕ → ℝ := fun j => T0 * 2 ^ j
  have hT2pos : ∀ j, 0 < T2p j := fun j => mul_pos T0pos (by positivity)
  let I : (ℕ ⊕ ℕ) ⊕ (ℕ ⊕ ℕ) → Set ℝ :=
    Sum.elim (Sum.elim (fun m => Set.Ioc (T1p m) (T1p m + H))
        (fun m => Set.Ioc (T1n m) (T1n m + H)))
      (Sum.elim (fun j => Set.uIoc (T2p j) (2 * T2p j))
        (fun j => Set.uIoc (-T2p j) (2 * -T2p j)))
  let c : (ℕ ⊕ ℕ) ⊕ (ℕ ⊕ ℕ) → ℝ :=
    Sum.elim (Sum.elim (fun m => if |T1p m| ≤ 2 * T0 then 2 * A / max 1 (m : ℝ) else 0)
        (fun m => if |T1n m| ≤ 2 * T0 then 2 * A / max 1 (m : ℝ) else 0))
      (Sum.elim (fun j => if T2p j ≤ T then 2 * N / T2p j else 0)
        (fun j => if T2p j ≤ T then 2 * N / T2p j else 0))
  let s : Finset ((ℕ ⊕ ℕ) ⊕ (ℕ ⊕ ℕ)) :=
    ((range R).disjSum (range R)).disjSum ((range M).disjSum (range M))
  have hmaxpos : ∀ m : ℕ, (0 : ℝ) < max 1 (m : ℝ) := fun m => lt_of_lt_of_le one_pos (le_max_left _ _)
  have hc0 : ∀ i, 0 ≤ c i := by
    intro i
    rcases i with (m | m) | (j | j)
    · show 0 ≤ (if |T1p m| ≤ 2 * T0 then 2 * A / max 1 (m : ℝ) else 0)
      split_ifs
      · exact div_nonneg (by linarith) (hmaxpos m).le
      · exact le_rfl
    · show 0 ≤ (if |T1n m| ≤ 2 * T0 then 2 * A / max 1 (m : ℝ) else 0)
      split_ifs
      · exact div_nonneg (by linarith) (hmaxpos m).le
      · exact le_rfl
    · show 0 ≤ (if T2p j ≤ T then 2 * N / T2p j else 0)
      split_ifs
      · exact div_nonneg (by positivity) (hT2pos j).le
      · exact le_rfl
    · show 0 ≤ (if T2p j ≤ T then 2 * N / T2p j else 0)
      split_ifs
      · exact div_nonneg (by positivity) (hT2pos j).le
      · exact le_rfl
  -- the dyadic range has `≪ L` pieces
  have hNq : (q : ℝ) ≤ N := by
    have hLc1 : L ^ (-c1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
    have h2 : A ^ 2 / N ≤ N := by rw [div_le_iff₀ Npos]; nlinarith
    calc (q : ℝ) ≤ A ^ 2 / N * L ^ (-c1) := hq3
      _ ≤ A ^ 2 / N * 1 := mul_le_mul_of_nonneg_left hLc1 (by positivity)
      _ ≤ N := by rw [mul_one]; exact h2
  have hTle : T ≤ N * N ^ (2 * ε) * T0 := by
    have hq12 : (q : ℝ) ^ (1 / 2 : ℝ) ≤ N := by
      calc (q : ℝ) ^ (1 / 2 : ℝ) ≤ (q : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hq1r (by norm_num)
        _ = q := Real.rpow_one _
        _ ≤ N := hNq
    have hin : H + |lam| * N ≤ T0 := by
      nlinarith [hT0, mul_nonneg (show (0 : ℝ) ≤ 4 * π - 1 by linarith) (add_nonneg hlN Hpos.le)]
    show (q : ℝ) ^ (1 / 2 : ℝ) * (N / A + |lam| * N) * (N : ℝ) ^ (2 * ε) ≤ _
    calc (q : ℝ) ^ (1 / 2 : ℝ) * (N / A + |lam| * N) * (N : ℝ) ^ (2 * ε)
        ≤ N * T0 * (N : ℝ) ^ (2 * ε) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hq12 hin (by positivity) Npos.le)
            (Real.rpow_nonneg Npos.le _)
      _ = N * N ^ (2 * ε) * T0 := by ring
  have hjM : ∀ j : ℕ, (2 : ℝ) ^ j ≤ N * N ^ (2 * ε) → j ∈ range M := by
    intro j hj
    have hlog : (j : ℝ) * Real.log 2 ≤ L + 2 * ε * L := by
      have := Real.log_le_log (by positivity) hj
      rw [Real.log_pow, Real.log_mul Npos.ne' (Real.rpow_pos_of_pos Npos _).ne',
        Real.log_rpow Npos] at this
      linarith
    have hl2 : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hjx : (j : ℝ) ≤ 2 * (1 + 2 * ε) * L := by
      nlinarith [mul_nonneg hj0 (le_of_lt (sub_pos.2 hl2))]
    rw [Finset.mem_range, hMdef]
    have := Nat.le_floor hjx
    omega
  have hTT0 : ∀ t, t ≤ T → t / T0 ≤ N * N ^ (2 * ε) := by
    intro t ht
    rw [div_le_iff₀ T0pos]
    linarith
  -- every `t` in `[-T, T]` lies in a piece whose weight dominates `wt38`
  have hcov : ∀ t ∈ Set.Icc (-T) T,
      wt38 N A lam t ≤ ∑ i ∈ s, (I i).indicator (fun _ => c i) t := by
    intro t ht
    have hpick : ∀ i ∈ s, t ∈ I i → wt38 N A lam t ≤ c i →
        wt38 N A lam t ≤ ∑ i ∈ s, (I i).indicator (fun _ => c i) t := by
      intro i hi hti hwc
      refine hwc.trans (le_trans (le_of_eq ?_) (Finset.single_le_sum
        (f := fun i => (I i).indicator (fun _ => c i) t)
        (fun k _ => Set.indicator_nonneg (fun _ _ => hc0 k) t) hi))
      show c i = (I i).indicator (fun _ => c i) t
      rw [Set.indicator_of_mem hti]
    have hRb : ∀ m : ℕ, (m : ℝ) ≤ 2 * T0 / H → m ∈ range R := by
      intro m hm
      rw [Finset.mem_range, hRdef]
      have h1 : (m : ℝ) ≤ ⌈2 * T0 / H⌉₊ := hm.trans (Nat.le_ceil _)
      have h2 : m ≤ ⌈2 * T0 / H⌉₊ := by exact_mod_cast h1
      omega
    by_cases hsmall : |t| ≤ T0
    · have ht1 := abs_le.1 hsmall
      by_cases hts : s0 < t
      · set x := (t - s0) / H with hx
        have hxpos : 0 < x := div_pos (by linarith) Hpos
        have hxH : x * H = t - s0 := by rw [hx]; field_simp
        have hcx : 1 ≤ ⌈x⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.2 hxpos).ne'
        set m := ⌈x⌉₊ - 1 with hm
        have hmc' : m + 1 = ⌈x⌉₊ := by omega
        have hmc : (m : ℝ) + 1 = ⌈x⌉₊ := by exact_mod_cast hmc'
        have hlt : (m : ℝ) < x := by have := Nat.ceil_lt_add_one hxpos.le; linarith
        have hle : x ≤ (m : ℝ) + 1 := by rw [hmc]; exact Nat.le_ceil x
        have hA' : (m : ℝ) * H < t - s0 := by rw [← hxH]; exact mul_lt_mul_of_pos_right hlt Hpos
        have hB' : t - s0 ≤ ((m : ℝ) + 1) * H := by
          rw [← hxH]; exact mul_le_mul_of_nonneg_right hle Hpos.le
        have he : ((m : ℝ) + 1) * H = m * H + H := by ring
        have hmR : m ∈ range R := by
          apply hRb
          have hx2 : x ≤ 2 * T0 / H := by
            rw [hx]; apply div_le_div_of_nonneg_right _ Hpos.le; linarith
          linarith
        apply hpick (Sum.inl (Sum.inl m)) (by simp [s, hmR])
        · show t ∈ Set.Ioc (T1p m) (T1p m + H)
          constructor
          · show s0 + m * H < t
            linarith
          · show t ≤ s0 + m * H + H
            linarith
        · show wt38 N A lam t ≤ (if |T1p m| ≤ 2 * T0 then 2 * A / max 1 (m : ℝ) else 0)
          rw [if_pos]
          · apply hwm m t
            rw [abs_of_pos (by linarith)]
            linarith
          · show |s0 + m * H| ≤ 2 * T0
            rw [abs_le]; constructor <;> linarith
      · push_neg at hts
        set x := (s0 - t) / H with hx
        have hx0 : 0 ≤ x := div_nonneg (by linarith) Hpos.le
        have hxH : x * H = s0 - t := by rw [hx]; field_simp
        set m := ⌊x⌋₊ with hm
        have hle : (m : ℝ) ≤ x := Nat.floor_le hx0
        have hlt : x < (m : ℝ) + 1 := Nat.lt_floor_add_one x
        have hA' : (m : ℝ) * H ≤ s0 - t := by
          rw [← hxH]; exact mul_le_mul_of_nonneg_right hle Hpos.le
        have hB' : s0 - t < ((m : ℝ) + 1) * H := by
          rw [← hxH]; exact mul_lt_mul_of_pos_right hlt Hpos
        have he : ((m : ℝ) + 1) * H = m * H + H := by ring
        have hmR : m ∈ range R := by
          apply hRb
          have hx2 : x ≤ 2 * T0 / H := by
            rw [hx]; apply div_le_div_of_nonneg_right _ Hpos.le; linarith
          linarith
        apply hpick (Sum.inl (Sum.inr m)) (by simp [s, hmR])
        · show t ∈ Set.Ioc (T1n m) (T1n m + H)
          constructor
          · show s0 - (m + 1) * H < t
            linarith
          · show t ≤ s0 - (m + 1) * H + H
            linarith
        · show wt38 N A lam t ≤ (if |T1n m| ≤ 2 * T0 then 2 * A / max 1 (m : ℝ) else 0)
          rw [if_pos]
          · apply hwm m t
            rw [abs_of_nonpos (by linarith)]
            linarith
          · show |s0 - (m + 1) * H| ≤ 2 * T0
            rw [abs_le]; constructor <;> linarith
    · push_neg at hsmall
      by_cases htpos : 0 < t
      · have habs : |t| = t := abs_of_pos htpos
        rw [habs] at hsmall
        obtain ⟨j, hj1, hj2⟩ :=
          exists_two_pow_between (t / T0) (by rw [one_lt_div T0pos]; exact hsmall)
        have hT2a : T0 * 2 ^ j < t := by rwa [lt_div_iff₀ T0pos, mul_comm] at hj1
        have hT2b : t ≤ 2 * (T0 * 2 ^ j) := by
          rw [div_le_iff₀ T0pos] at hj2
          have e : (2 : ℝ) ^ (j + 1) * T0 = 2 * (T0 * 2 ^ j) := by ring
          rw [e] at hj2
          exact hj2
        have hjm : j ∈ range M := hjM j (le_trans hj1.le (hTT0 t ht.2))
        apply hpick (Sum.inr (Sum.inl j)) (by simp [s, hjm])
        · show t ∈ Set.uIoc (T2p j) (2 * T2p j)
          rw [Set.mem_uIoc]
          exact Or.inl ⟨hT2a, hT2b⟩
        · show wt38 N A lam t ≤ (if T2p j ≤ T then 2 * N / T2p j else 0)
          rw [if_pos (show T0 * 2 ^ j ≤ T by linarith [ht.2])]
          calc wt38 N A lam t ≤ 2 * N / |t| := hwbig t (by rw [habs]; linarith)
            _ ≤ 2 * N / T2p j := by
              rw [habs]
              exact div_le_div_of_nonneg_left (by positivity) (hT2pos j) hT2a.le
      · push_neg at htpos
        have habs : |t| = -t := abs_of_nonpos htpos
        rw [habs] at hsmall
        obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near
          (show 1 ≤ -t / T0 by rw [one_le_div T0pos]; linarith) (by norm_num : (1 : ℝ) < 2)
        have hT2a : T0 * 2 ^ j ≤ -t := by rwa [le_div_iff₀ T0pos, mul_comm] at hj1
        have hT2b : -t < 2 * (T0 * 2 ^ j) := by
          rw [div_lt_iff₀ T0pos] at hj2
          have e : (2 : ℝ) ^ (j + 1) * T0 = 2 * (T0 * 2 ^ j) := by ring
          rw [e] at hj2
          exact hj2
        have hjm : j ∈ range M := hjM j (le_trans hj1 (hTT0 (-t) (by linarith [ht.1])))
        apply hpick (Sum.inr (Sum.inr j)) (by simp [s, hjm])
        · show t ∈ Set.uIoc (-T2p j) (2 * -T2p j)
          rw [Set.mem_uIoc]
          right
          constructor
          · show 2 * -(T0 * 2 ^ j) < t
            linarith
          · show t ≤ -(T0 * 2 ^ j)
            linarith
        · show wt38 N A lam t ≤ (if T2p j ≤ T then 2 * N / T2p j else 0)
          rw [if_pos (show T0 * 2 ^ j ≤ T by linarith [ht.1])]
          calc wt38 N A lam t ≤ 2 * N / |t| := hwbig t (by rw [habs]; linarith)
            _ ≤ 2 * N / T2p j := by
              rw [habs]
              exact div_le_div_of_nonneg_left (by positivity) (hT2pos j) hT2a
  -- integrate
  have hf : ∀ χ : DirichletCharacter ℂ q,
      Continuous (fun t : ℝ => ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖) :=
    fun χ => (Fprod_continuous Nv χ).norm
  have hIm : ∀ i, MeasurableSet (I i) := by
    intro i
    rcases i with (m | m) | (j | j)
    · exact measurableSet_Ioc
    · exact measurableSet_Ioc
    · exact measurableSet_uIoc
    · exact measurableSet_uIoc
  have hIi : ∀ χ : DirichletCharacter ℂ q, ∀ i,
      IntegrableOn (fun t : ℝ => ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖) (I i) := by
    intro χ i
    rcases i with (m | m) | (j | j)
    · exact (hf χ).integrableOn_Ioc
    · exact (hf χ).integrableOn_Ioc
    · exact (hf χ).integrableOn_uIoc
    · exact (hf χ).integrableOn_uIoc
  let S : (ℕ ⊕ ℕ) ⊕ (ℕ ⊕ ℕ) → ℝ := fun i =>
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
      ∫ t in I i, ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
  have hstep : ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
        ∫ t in Set.Icc (-T) T, wt38 N A lam t * ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
      ≤ ∑ i ∈ s, c i * S i := by
    calc ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.Icc (-T) T, wt38 N A lam t * ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
        ≤ ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
            ∑ i ∈ s, c i * ∫ t in I i, ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖ := by
          apply Finset.sum_le_sum
          intro χ _
          exact integral_le_pieces s I c (wt38 N A lam)
            (fun t => ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖) (-T) T hIm
            (fun i _ => hIi χ i) (fun i _ => hc0 i) hw0 (fun t => norm_nonneg _) hcov
      _ = ∑ i ∈ s, c i * S i := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          exact (Finset.mul_sum _ _ _).symm
  -- per-piece bounds from (3.11) and (3.12)
  set E := ((q : ℝ) * N) ^ (1 / 2 : ℝ) * A * L ^ (-B - (c0 + 1)) with hE
  have hX0 : 0 ≤ ((q : ℝ) * N) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hY0 : 0 ≤ L ^ (-B - (c0 + 1)) := Real.rpow_nonneg Lpos.le _
  have hE0 : 0 ≤ E := mul_nonneg (mul_nonneg hX0 Apos.le) hY0
  have hK1 : 0 ≤ max K1 0 := le_max_right _ _
  have hK2 : 0 ≤ max K2 0 := le_max_right _ _
  have hqN : ((q : ℝ) / N) ^ (1 / 2 : ℝ) * N = ((q : ℝ) * N) ^ (1 / 2 : ℝ) := by
    rw [Real.div_rpow (Nat.cast_nonneg _) Npos.le, Real.mul_rpow (Nat.cast_nonneg _) Npos.le]
    have hs : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = N := by
      rw [← Real.rpow_add Npos]; norm_num
    have hpos : 0 < (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos Npos _
    rw [div_mul_eq_mul_div, div_eq_iff hpos.ne', mul_assoc, hs]
  have hZ0 : 0 ≤ ((q : ℝ) / N) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hshortb : ∀ T1 : ℝ, |T1| ≤ 2 * T0 →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
        ∫ t in Set.Ioc T1 (T1 + H), ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
      ≤ max K1 0 * ((q : ℝ) * N) ^ (1 / 2 : ℝ) * L ^ (-B - (c0 + 1)) := by
    intro T1 hv
    refine le_trans (H1 N A lam q Nv T1 hNa hypa hc hv) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hX0) hY0
  have hdyb : ∀ T2 : ℝ, T0 ≤ |T2| → |T2| ≤ 2 * T →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
        ∫ t in Set.uIoc T2 (2 * T2), ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
      ≤ max K2 0 * ((q : ℝ) / N) ^ (1 / 2 : ℝ) * A * |T2| * L ^ (-B - (c0 + 1)) := by
    intro T2 hv1 hv2
    refine le_trans (H2 N A lam q Nv T2 hNb hypb hc hv1 hv2) ?_
    have hp : 0 ≤ ((q : ℝ) / N) ^ (1 / 2 : ℝ) * A * |T2| * L ^ (-B - (c0 + 1)) :=
      mul_nonneg (mul_nonneg (mul_nonneg hZ0 Apos.le) (abs_nonneg _)) hY0
    nlinarith [mul_le_mul_of_nonneg_right (le_max_left K2 0) hp]
  have hfam1 : ∀ m ∈ range R, c (Sum.inl (Sum.inl m)) * S (Sum.inl (Sum.inl m)) ≤
      2 / max 1 (m : ℝ) * (max K1 0 * E) := by
    intro m _
    have hm0 : (0 : ℝ) ≤ 2 / max 1 (m : ℝ) := div_nonneg (by norm_num) (hmaxpos m).le
    show (if |T1p m| ≤ 2 * T0 then 2 * A / max 1 (m : ℝ) else 0) * S (Sum.inl (Sum.inl m)) ≤ _
    split_ifs with hv
    · have hb := hshortb (T1p m) hv
      calc 2 * A / max 1 (m : ℝ) * S (Sum.inl (Sum.inl m))
          ≤ 2 * A / max 1 (m : ℝ) *
              (max K1 0 * ((q : ℝ) * N) ^ (1 / 2 : ℝ) * L ^ (-B - (c0 + 1))) :=
            mul_le_mul_of_nonneg_left hb (div_nonneg (by linarith) (hmaxpos m).le)
        _ = 2 / max 1 (m : ℝ) * (max K1 0 * E) := by rw [hE]; ring
    · rw [zero_mul]; exact mul_nonneg hm0 (mul_nonneg hK1 hE0)
  have hfam2 : ∀ m ∈ range R, c (Sum.inl (Sum.inr m)) * S (Sum.inl (Sum.inr m)) ≤
      2 / max 1 (m : ℝ) * (max K1 0 * E) := by
    intro m _
    have hm0 : (0 : ℝ) ≤ 2 / max 1 (m : ℝ) := div_nonneg (by norm_num) (hmaxpos m).le
    show (if |T1n m| ≤ 2 * T0 then 2 * A / max 1 (m : ℝ) else 0) * S (Sum.inl (Sum.inr m)) ≤ _
    split_ifs with hv
    · have hb := hshortb (T1n m) hv
      calc 2 * A / max 1 (m : ℝ) * S (Sum.inl (Sum.inr m))
          ≤ 2 * A / max 1 (m : ℝ) *
              (max K1 0 * ((q : ℝ) * N) ^ (1 / 2 : ℝ) * L ^ (-B - (c0 + 1))) :=
            mul_le_mul_of_nonneg_left hb (div_nonneg (by linarith) (hmaxpos m).le)
        _ = 2 / max 1 (m : ℝ) * (max K1 0 * E) := by rw [hE]; ring
    · rw [zero_mul]; exact mul_nonneg hm0 (mul_nonneg hK1 hE0)
  have hfam3 : ∀ j ∈ range M, c (Sum.inr (Sum.inl j)) * S (Sum.inr (Sum.inl j)) ≤
      2 * (max K2 0 * E) := by
    intro j _
    show (if T2p j ≤ T then 2 * N / T2p j else 0) * S (Sum.inr (Sum.inl j)) ≤ _
    have hp := hT2pos j
    split_ifs with hv
    · have hv1 : T0 ≤ |T2p j| := by
        rw [abs_of_pos hp]
        exact le_mul_of_one_le_right T0pos.le (one_le_pow₀ (by norm_num))
      have hv2 : |T2p j| ≤ 2 * T := by rw [abs_of_pos hp]; linarith
      have hb := hdyb (T2p j) hv1 hv2
      rw [abs_of_pos hp] at hb
      calc 2 * N / T2p j * S (Sum.inr (Sum.inl j))
          ≤ 2 * N / T2p j * (max K2 0 * ((q : ℝ) / N) ^ (1 / 2 : ℝ) * A * T2p j *
              L ^ (-B - (c0 + 1))) :=
            mul_le_mul_of_nonneg_left hb (div_nonneg (by positivity) hp.le)
        _ = 2 * (max K2 0 * ((((q : ℝ) / N) ^ (1 / 2 : ℝ) * N) * A * L ^ (-B - (c0 + 1)))) := by
            field_simp
        _ = 2 * (max K2 0 * E) := by rw [hqN]
    · rw [zero_mul]; exact mul_nonneg (by norm_num) (mul_nonneg hK2 hE0)
  have hfam4 : ∀ j ∈ range M, c (Sum.inr (Sum.inr j)) * S (Sum.inr (Sum.inr j)) ≤
      2 * (max K2 0 * E) := by
    intro j _
    show (if T2p j ≤ T then 2 * N / T2p j else 0) * S (Sum.inr (Sum.inr j)) ≤ _
    have hp := hT2pos j
    split_ifs with hv
    · have hv1 : T0 ≤ |-T2p j| := by
        rw [abs_neg, abs_of_pos hp]
        exact le_mul_of_one_le_right T0pos.le (one_le_pow₀ (by norm_num))
      have hv2 : |-T2p j| ≤ 2 * T := by rw [abs_neg, abs_of_pos hp]; linarith
      have hb := hdyb (-T2p j) hv1 hv2
      rw [abs_neg, abs_of_pos hp] at hb
      calc 2 * N / T2p j * S (Sum.inr (Sum.inr j))
          ≤ 2 * N / T2p j * (max K2 0 * ((q : ℝ) / N) ^ (1 / 2 : ℝ) * A * T2p j *
              L ^ (-B - (c0 + 1))) :=
            mul_le_mul_of_nonneg_left hb (div_nonneg (by positivity) hp.le)
        _ = 2 * (max K2 0 * ((((q : ℝ) / N) ^ (1 / 2 : ℝ) * N) * A * L ^ (-B - (c0 + 1)))) := by
            field_simp
        _ = 2 * (max K2 0 * E) := by rw [hqN]
    · rw [zero_mul]; exact mul_nonneg (by norm_num) (mul_nonneg hK2 hE0)
  -- the harmonic sum and the count of dyadic pieces
  have hy : 2 * T0 / H ≤ 2 * N + 32 := by
    have e : 2 * T0 / H = 8 * π * (|lam| * A) + 8 * π := by
      have hAH : A * H = N := by rw [hHdef]; field_simp
      rw [div_eq_iff Hpos.ne']
      linear_combination 2 * hT0 - 8 * π * |lam| * hAH
    rw [e]
    nlinarith
  have hypos : 0 < 2 * T0 / H := div_pos (by linarith) Hpos
  have hceil : (⌈2 * T0 / H⌉₊ : ℝ) ≤ (N : ℝ) ^ 2 := by
    have := Nat.ceil_lt_add_one hypos.le
    nlinarith
  have hlogc : Real.log (⌈2 * T0 / H⌉₊ : ℝ) ≤ 2 * L := by
    have hpos : (0 : ℝ) < ⌈2 * T0 / H⌉₊ := by exact_mod_cast Nat.ceil_pos.2 hypos
    calc Real.log (⌈2 * T0 / H⌉₊ : ℝ) ≤ Real.log ((N : ℝ) ^ 2) := Real.log_le_log hpos hceil
      _ = 2 * L := by rw [Real.log_pow, hLdef]; norm_num
  have hharm : ∑ m ∈ range R, 1 / max 1 (m : ℝ) ≤ 2 + 2 * L :=
    (sum_inv_max_le ⌈2 * T0 / H⌉₊).trans (by linarith)
  have hshort : ∑ m ∈ range R, 2 / max 1 (m : ℝ) * (max K1 0 * E) ≤
      (2 + 2 * L) * (2 * (max K1 0 * E)) := by
    calc ∑ m ∈ range R, 2 / max 1 (m : ℝ) * (max K1 0 * E)
        = (∑ m ∈ range R, 1 / max 1 (m : ℝ)) * (2 * (max K1 0 * E)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro m _
          ring
      _ ≤ (2 + 2 * L) * (2 * (max K1 0 * E)) :=
          mul_le_mul_of_nonneg_right hharm (by positivity)
  have hMle : (M : ℝ) ≤ (3 + 4 * ε) * L := by
    have h1 : (M : ℝ) = (⌊2 * (1 + 2 * ε) * L⌋₊ : ℝ) + 1 := by rw [hMdef]; push_cast; ring
    have h2 := Nat.floor_le (show 0 ≤ 2 * (1 + 2 * ε) * L by positivity)
    rw [h1]
    nlinarith
  have hdy : ∑ j ∈ range M, 2 * (max K2 0 * E) = M * (2 * (max K2 0 * E)) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hLexp : L ^ (-B - c0) = L ^ (-B - (c0 + 1)) * L := by
    rw [← Real.rpow_add_one Lpos.ne']
    congr 1
    ring
  have hsplit : ∑ i ∈ s, c i * S i =
      (∑ m ∈ range R, c (Sum.inl (Sum.inl m)) * S (Sum.inl (Sum.inl m)) +
        ∑ m ∈ range R, c (Sum.inl (Sum.inr m)) * S (Sum.inl (Sum.inr m))) +
      (∑ j ∈ range M, c (Sum.inr (Sum.inl j)) * S (Sum.inr (Sum.inl j)) +
        ∑ j ∈ range M, c (Sum.inr (Sum.inr j)) * S (Sum.inr (Sum.inr j))) := by
    simp only [s, Finset.sum_disjSum]
  have hKE1 : 0 ≤ max K1 0 * E := mul_nonneg hK1 hE0
  have hKE2 : 0 ≤ max K2 0 * E := mul_nonneg hK2 hE0
  calc ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
        ∫ t in Set.Icc (-T) T, wt38 N A lam t * ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
      ≤ ∑ i ∈ s, c i * S i := hstep
    _ ≤ (∑ m ∈ range R, 2 / max 1 (m : ℝ) * (max K1 0 * E) +
          ∑ m ∈ range R, 2 / max 1 (m : ℝ) * (max K1 0 * E)) +
        (∑ j ∈ range M, 2 * (max K2 0 * E) + ∑ j ∈ range M, 2 * (max K2 0 * E)) := by
        rw [hsplit]
        exact add_le_add (add_le_add (Finset.sum_le_sum hfam1) (Finset.sum_le_sum hfam2))
          (add_le_add (Finset.sum_le_sum hfam3) (Finset.sum_le_sum hfam4))
    _ ≤ 2 * ((2 + 2 * L) * (2 * (max K1 0 * E))) + 2 * (M * (2 * (max K2 0 * E))) := by
        rw [hdy]; linarith [hshort]
    _ ≤ (12 * max K1 0 + 4 * (3 + 4 * ε) * max K2 0) * E * L := by
        have h1 := mul_le_mul_of_nonneg_right (show 4 * (2 + 2 * L) ≤ 12 * L by linarith) hKE1
        have h2 := mul_le_mul_of_nonneg_right hMle hKE2
        nlinarith
    _ = (12 * max K1 0 + 4 * (3 + 4 * ε) * max K2 0) * ((q : ℝ) * N) ^ (1 / 2 : ℝ) * A *
          Real.log N ^ (-B - c0) := by
        rw [hLexp, hE]; ring

end

end LeanLab.Zhan1991
