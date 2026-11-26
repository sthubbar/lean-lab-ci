import LeanLab.ExceptionalSet.Decomp553a

/-!
Shared core of the three Feed 1122 parity removal leaves
`Decomp553b.feed1122_high_j0_parity_removal`,
`Decomp553d.feed1122_high_j1_parity_removal` and
`Decomp553c.leaf_low_j1_parity_shift`.

Source: J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998), paper P0082, section 7 on page 370, displays (40)
and (41), with Lemma 4 on page 359.

The proof of displays (40) and (41) has two analytic inputs, the two leaves here.

  * `leaf_parity_trapezoid_fourier` is display (40): the indicator of
    `⌊x⌋ ≡ 0 mod 2` agrees, for `x` at distance at least `A` from the integers, with
    the trapezoid function of ramp width `A`, whose Fourier coefficients in the
    frequencies `h / 2` satisfy `c_h ≪ min(1, A ^ (-1) h ^ (-2))`. Truncating at
    `|h| ≤ H` costs `≪ A ^ (-1) H ^ (-1)`, the kept coefficients have total size
    `≪ A ^ (-1 / 2)`, and everywhere the difference is at most `2` plus the tail.
  * `leaf_lemma4_unit_upper` is Lemma 4 on page 359 at `α = 1`, in the upper bound
    form the paper says suffices: the number of `N / 2 < n ≤ N` with
    `z₁ ≤ {F(n)} < z₂` is at most `(z₂ - z₁) N + C N ℰ ^ (-1)`.

Everything else is proved: the finite Fourier expansion of the restricted sum,
display (41), the count of the `n` near a jump by Lemma 4, and the bookkeeping
with `A = ℰ ^ (-1)` and truncation `H = ⌊ℰ ^ 2⌋`, giving the bound
`N ℰ ^ (-5 / 6)` for the parity restricted sum over any sub-block of
`(N / 2, N]`, for every shift `F(n) - j`, whenever all shifted plain sums at
`t + h / 2`, `|h| ≤ ℰ ^ 2`, are at most `N ℰ ^ (-2)`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Feed1122ParityCore

open Real Finset
open LeanLab.ExceptionalSet.U1539 (eC calE)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- LEAF: P0082 section 7 page 370, display (40): the trapezoid function. For
`0 < A ≤ 1 / 4` the periodic function equal to one on `[k + A, k + 1 - A]` for
`k` even, zero on it for `k` odd, and linear on the ramps of width `2 A` around
the integers, has Fourier coefficients `c_h` in the frequencies `h / 2` with
`|c_h| ≪ min(1, A ^ (-1) h ^ (-2))`, by Poisson summation. Hence after truncation
at `|h| ≤ H` the kept coefficients have total size `≪ A ^ (-1 / 2)`, the tail is
`≪ A ^ (-1) H ^ (-1)`, the trapezoid equals the indicator of `⌊x⌋` even off the
ramps, and it lies in `[0, 1]` everywhere. Class MEDIUM, a self contained
Fourier computation on the circle with no arithmetic input. -/
theorem leaf_parity_trapezoid_fourier :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 0 < A → A ≤ 1 / 4 → ∀ H : ℕ, 1 ≤ H →
      ∃ c : ℤ → ℂ, (∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖c h‖) ≤ C * A ^ (-(1 / 2 : ℝ)) ∧
        ∀ x : ℝ,
          ‖(if Even ⌊x⌋ then (1 : ℂ) else 0) -
              ∑ h ∈ Finset.Icc (-(H : ℤ)) H, c h * eC ((h : ℝ) / 2 * x)‖ ≤
            (if A ≤ Int.fract x ∧ Int.fract x ≤ 1 - A then C / (A * H)
              else 2 + C / (A * H)) := by
  sorry

/-- LEAF: P0082 Lemma 4 on page 359 at `α = 1`, in the upper bound form that the
paper notes suffices, with `[BP]` for a simple proof from Theorem 2: there is
`K > 0` such that for `0 < k < K`, uniformly in `0 ≤ z₁ ≤ z₂ ≤ 1`, the number of
`N / 2 < n ≤ N` with `z₁ ≤ {F(n)} < z₂` is at most
`(z₂ - z₁) N + O(N exp(-k (log N) ^ (3 - 2 γ)))`. Class HARD, a cited
consequence of Theorem 2 by Vinogradov's argument. -/
theorem leaf_lemma4_unit_upper (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ k : ℝ, 0 < k → k < K →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ z₁ z₂ : ℝ, 0 ≤ z₁ → z₁ ≤ z₂ → z₂ ≤ 1 →
        (((Finset.Ioc (N / 2) N).filter
            (fun n : ℕ => z₁ ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < z₂)).card : ℝ) ≤
          (z₂ - z₁) * N + C * N * (calE γ k N)⁻¹ := by
  sorry

theorem eC_add (a b : ℝ) : eC (a + b) = eC a * eC b := by
  unfold U1539.eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem eC_norm (x : ℝ) : ‖eC x‖ = 1 := by
  unfold U1539.eC
  rw [Complex.norm_exp]
  simp

/-- Proved helper: a shift `F(n) - j` multiplies every term of a phase sum by the
same unimodular factor, so the norm does not change. -/
theorem shift_sum_norm (B : Finset ℕ) (v : ℕ → ℝ) (s : ℝ) (j : ℤ) :
    ‖∑ n ∈ B, eC (s * (v n - j))‖ = ‖∑ n ∈ B, eC (s * v n)‖ := by
  have : ∑ n ∈ B, eC (s * (v n - j)) = (∑ n ∈ B, eC (s * v n)) * eC (-(s * j)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [← eC_add]; congr 1; ring
  rw [this, norm_mul, eC_norm, mul_one]

/-- Proved, P0082 page 370 display (41): the finite Fourier expansion of the
parity restricted sum, with the triangle inequality. -/
theorem parity_removal_generic (B : Finset ℕ) (p : ℕ → Prop) [DecidablePred p]
    (g : ℕ → Prop) [DecidablePred g] (f : ℕ → ℝ) (t : ℝ) (I : Finset ℤ) (c : ℤ → ℂ)
    (η Kb V S : ℝ) (hV : 0 ≤ V)
    (hind : ∀ n ∈ B, ‖(if p n then (1 : ℂ) else 0) -
        ∑ h ∈ I, c h * eC ((h : ℝ) / 2 * f n)‖ ≤ if g n then η else Kb)
    (hS : (∑ h ∈ I, ‖c h‖) ≤ S)
    (hsum : ∀ h ∈ I, ‖∑ n ∈ B, eC ((t + (h : ℝ) / 2) * f n)‖ ≤ V) :
    ‖∑ n ∈ B.filter p, eC (t * f n)‖ ≤
      S * V + η * ((B.filter g).card : ℝ) + Kb * ((B.filter (fun n : ℕ => ¬ g n)).card : ℝ) := by
  have hsplit : ∑ n ∈ B.filter p, eC (t * f n) =
      ∑ h ∈ I, c h * ∑ n ∈ B, eC ((t + (h : ℝ) / 2) * f n) +
      ∑ n ∈ B, ((if p n then (1 : ℂ) else 0) - ∑ h ∈ I, c h * eC ((h : ℝ) / 2 * f n)) *
        eC (t * f n) := by
    rw [Finset.sum_filter]
    have h1 : ∀ n ∈ B, (if p n then eC (t * f n) else 0) =
        (∑ h ∈ I, c h * eC ((h : ℝ) / 2 * f n)) * eC (t * f n) +
        ((if p n then (1 : ℂ) else 0) - ∑ h ∈ I, c h * eC ((h : ℝ) / 2 * f n)) *
          eC (t * f n) := by
      intro n _
      split_ifs <;> ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
    congr 1
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun n _ => ?_))
    rw [show (t + (h : ℝ) / 2) * f n = (h : ℝ) / 2 * f n + t * f n by ring, eC_add]
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hA : ‖∑ h ∈ I, c h * ∑ n ∈ B, eC ((t + (h : ℝ) / 2) * f n)‖ ≤ S * V := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ h ∈ I, ‖c h * ∑ n ∈ B, eC ((t + (h : ℝ) / 2) * f n)‖
        ≤ ∑ h ∈ I, ‖c h‖ * V := by
          refine Finset.sum_le_sum (fun h hh => ?_)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hsum h hh) (norm_nonneg _)
      _ = (∑ h ∈ I, ‖c h‖) * V := by rw [Finset.sum_mul]
      _ ≤ S * V := mul_le_mul_of_nonneg_right hS hV
  have hB : ‖∑ n ∈ B, ((if p n then (1 : ℂ) else 0) -
      ∑ h ∈ I, c h * eC ((h : ℝ) / 2 * f n)) * eC (t * f n)‖ ≤
      η * ((B.filter g).card : ℝ) + Kb * ((B.filter (fun n : ℕ => ¬ g n)).card : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ B, ‖((if p n then (1 : ℂ) else 0) -
          ∑ h ∈ I, c h * eC ((h : ℝ) / 2 * f n)) * eC (t * f n)‖
        ≤ ∑ n ∈ B, (if g n then η else Kb) := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          rw [norm_mul, eC_norm, mul_one]
          exact hind n hn
      _ = η * ((B.filter g).card : ℝ) + Kb * ((B.filter (fun n : ℕ => ¬ g n)).card : ℝ) := by
          rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
          ring
  linarith

/-- Proved, P0082 page 370 after display (41): the parity restricted sum over any
sub-block `B` of `(N / 2, N]`, for the shift `F(n) - j`, is at most `N ℰ ^ (-5 / 6)`
once all plain sums at `t + h / 2`, `|h| ≤ ℰ ^ 2`, are at most `N ℰ ^ (-2)`.
Uses `A = ℰ ^ (-1)` and `H = ⌊ℰ ^ 2⌋`. CONDITIONAL ON the two leaves above. -/
theorem parity_core (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ B : Finset ℕ, B ⊆ Finset.Ioc (N / 2) N →
        ∀ (j : ℤ) (t : ℝ),
          (∀ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (2 : ℝ) →
            ‖∑ n ∈ B, eC ((t + (h : ℝ) / 2) * (F γ n - j))‖ ≤
              (N : ℝ) * calE γ κ N ^ (-2 : ℝ)) →
          ‖∑ n ∈ B.filter (fun n : ℕ => Even ⌊F γ n - j⌋), eC (t * (F γ n - j))‖ ≤
            (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) := by
  obtain ⟨C1, hC1, HL1⟩ := leaf_parity_trapezoid_fourier
  obtain ⟨K, hK, HL2⟩ := leaf_lemma4_unit_upper γ h1 h2
  refine ⟨K / 2, by linarith, fun κ hκ hκs => ?_⟩
  obtain ⟨C2, hC2, N₂, HL2⟩ := HL2 κ hκ (by linarith)
  have hlog : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hE : Filter.Tendsto (fun N : ℕ => calE γ κ N) Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp
      (((tendsto_rpow_atTop (by linarith : 0 < 3 - 2 * γ)).comp hlog).const_mul_atTop hκ)
  set M : ℝ := 3 * C1 + (2 + C1) * (2 * (1 + C2)) with hM
  obtain ⟨N₁, HN₁⟩ := Filter.eventually_atTop.mp
    ((hE.eventually_ge_atTop 4).and
      (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp hE).eventually_ge_atTop M))
  refine ⟨max N₁ N₂, fun N hN B hB j t hhyp => ?_⟩
  obtain ⟨hE4, hEM⟩ := HN₁ N ((le_max_left _ _).trans hN)
  have hN2 : N₂ ≤ N := (le_max_right _ _).trans hN
  change M ≤ calE γ κ N ^ (1 / 6 : ℝ) at hEM
  set E := calE γ κ N with hEdef
  have hE0 : 0 < E := by linarith
  have hE1 : 1 ≤ E := by linarith
  set A : ℝ := E⁻¹ with hAdef
  have hA0 : 0 < A := inv_pos.mpr hE0
  have hA4 : A ≤ 1 / 4 := by
    rw [hAdef]; exact inv_le_of_inv_le₀ (by norm_num) (by norm_num; linarith)
  have hE2 : E ^ (2 : ℝ) = E ^ 2 := by norm_cast
  set H : ℕ := ⌊E ^ (2 : ℝ)⌋₊ with hHdef
  have hHle : (H : ℝ) ≤ E ^ 2 := by
    rw [← hE2]; exact Nat.floor_le (by positivity)
  have hHlt : E ^ 2 < (H : ℝ) + 1 := by
    rw [← hE2]; exact Nat.lt_floor_add_one _
  have hE16 : 16 ≤ E ^ 2 := by nlinarith
  have hHge : E ^ 2 / 2 ≤ (H : ℝ) := by linarith
  have hH1 : 1 ≤ H := by
    have : (1 : ℝ) ≤ H := by linarith
    exact_mod_cast this
  obtain ⟨c, hcS, hcx⟩ := HL1 A hA0 hA4 H hH1
  have hNR : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hV : 0 ≤ (N : ℝ) * E ^ (-2 : ℝ) := mul_nonneg hNR (by positivity)
  have key := parity_removal_generic B (fun n : ℕ => Even ⌊F γ n - j⌋)
    (fun n : ℕ => A ≤ Int.fract (F γ n - j) ∧ Int.fract (F γ n - j) ≤ 1 - A)
    (fun n : ℕ => F γ n - j) t (Finset.Icc (-(H : ℤ)) H) c (C1 / (A * H)) (2 + C1 / (A * H))
    ((N : ℝ) * E ^ (-2 : ℝ)) (C1 * A ^ (-(1 / 2 : ℝ))) hV
    (fun n _ => hcx (F γ n - j)) hcS (fun h hh => by
      apply hhyp h
      have hh' := Finset.mem_Icc.mp hh
      have : |h| ≤ (H : ℤ) := abs_le.mpr ⟨hh'.1, hh'.2⟩
      have : (|h| : ℝ) ≤ (H : ℝ) := by exact_mod_cast this
      rw [hE2]; linarith)
  -- card bounds
  have hcardB : ((B.filter (fun n : ℕ => A ≤ Int.fract (F γ n - j) ∧
      Int.fract (F γ n - j) ≤ 1 - A)).card : ℝ) ≤ N := by
    have h1 := Finset.card_le_card ((Finset.filter_subset (fun n : ℕ => A ≤ Int.fract (F γ n - j) ∧
      Int.fract (F γ n - j) ≤ 1 - A) B).trans hB)
    have h2 : (Finset.Ioc (N / 2) N).card ≤ N := by rw [Nat.card_Ioc]; omega
    exact_mod_cast h1.trans h2
  have hbad : ((B.filter (fun n : ℕ => ¬ (A ≤ Int.fract (F γ n - j) ∧
      Int.fract (F γ n - j) ≤ 1 - A))).card : ℝ) ≤ 2 * (1 + C2) * N * E⁻¹ := by
    have hsub : B.filter (fun n : ℕ => ¬ (A ≤ Int.fract (F γ n - j) ∧
        Int.fract (F γ n - j) ≤ 1 - A)) ⊆
        (Finset.Ioc (N / 2) N).filter
          (fun n : ℕ => 0 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < A) ∪
        (Finset.Ioc (N / 2) N).filter
          (fun n : ℕ => 1 - A ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < 1) := by
      intro n hn
      rw [Finset.mem_filter] at hn
      obtain ⟨hnB, hng⟩ := hn
      have hfr : Int.fract (F γ n - j) = Int.fract (F γ n) := Int.fract_sub_intCast _ _
      rw [hfr] at hng
      have h0 := Int.fract_nonneg (F γ n)
      have h1' := Int.fract_lt_one (F γ n)
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases hlo : Int.fract (F γ n) < A
      · exact Or.inl ⟨hB hnB, h0, hlo⟩
      · right
        refine ⟨hB hnB, ?_, h1'⟩
        by_contra hc
        exact hng ⟨not_lt.mp hlo, (not_le.mp hc).le⟩
    have hc1 := HL2 N hN2 0 A le_rfl hA0.le (by linarith)
    have hc2 := HL2 N hN2 (1 - A) 1 (by linarith) (by linarith) le_rfl
    have hu := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hu' : ((B.filter (fun n : ℕ => ¬ (A ≤ Int.fract (F γ n - j) ∧
        Int.fract (F γ n - j) ≤ 1 - A))).card : ℝ) ≤
        (((Finset.Ioc (N / 2) N).filter
          (fun n : ℕ => 0 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < A)).card : ℝ) +
        (((Finset.Ioc (N / 2) N).filter
          (fun n : ℕ => 1 - A ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < 1)).card : ℝ) := by
      exact_mod_cast hu
    have : (A - 0) * N + C2 * N * E⁻¹ + ((1 - (1 - A)) * N + C2 * N * E⁻¹) =
        2 * (1 + C2) * N * E⁻¹ := by rw [hAdef]; ring
    linarith
  -- the numeric parameters
  have hS : C1 * A ^ (-(1 / 2 : ℝ)) * ((N : ℝ) * E ^ (-2 : ℝ)) ≤ C1 * N * E⁻¹ := by
    have hAp : A ^ (-(1 / 2 : ℝ)) = E ^ (1 / 2 : ℝ) := by
      rw [hAdef, Real.inv_rpow hE0.le, ← Real.rpow_neg hE0.le]; norm_num
    rw [hAp]
    have hp : E ^ (1 / 2 : ℝ) * E ^ (-2 : ℝ) ≤ E⁻¹ := by
      rw [← Real.rpow_add hE0, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hE1 (by norm_num)
    have := mul_le_mul_of_nonneg_left hp (mul_nonneg hC1.le hNR)
    calc C1 * E ^ (1 / 2 : ℝ) * ((N : ℝ) * E ^ (-2 : ℝ))
        = C1 * N * (E ^ (1 / 2 : ℝ) * E ^ (-2 : ℝ)) := by ring
      _ ≤ C1 * N * E⁻¹ := this
  have hη : C1 / (A * H) ≤ 2 * C1 * E⁻¹ := by
    have hAH : E / 2 ≤ A * H := by
      rw [hAdef, le_inv_mul_iff₀ hE0]
      nlinarith
    calc C1 / (A * H) ≤ C1 / (E / 2) :=
          div_le_div_of_nonneg_left hC1.le (by linarith) hAH
      _ = 2 * C1 * E⁻¹ := by field_simp
  have hη1 : C1 / (A * H) ≤ C1 := by
    have : 2 * C1 * E⁻¹ ≤ C1 := by
      have hEi : E⁻¹ ≤ 1 / 4 := by rw [← hAdef]; exact hA4
      nlinarith
    linarith
  have hEi0 : 0 ≤ E⁻¹ := by positivity
  have hfin : C1 * A ^ (-(1 / 2 : ℝ)) * ((N : ℝ) * E ^ (-2 : ℝ)) +
      C1 / (A * H) * ((B.filter (fun n : ℕ => A ≤ Int.fract (F γ n - j) ∧
        Int.fract (F γ n - j) ≤ 1 - A)).card : ℝ) +
      (2 + C1 / (A * H)) * ((B.filter (fun n : ℕ => ¬ (A ≤ Int.fract (F γ n - j) ∧
        Int.fract (F γ n - j) ≤ 1 - A))).card : ℝ) ≤ M * N * E⁻¹ := by
    have hηn : 0 ≤ C1 / (A * H) := by positivity
    have t2 : C1 / (A * H) * ((B.filter (fun n : ℕ => A ≤ Int.fract (F γ n - j) ∧
        Int.fract (F γ n - j) ≤ 1 - A)).card : ℝ) ≤ 2 * C1 * E⁻¹ * N :=
      mul_le_mul hη hcardB (Nat.cast_nonneg _) (by positivity)
    have t3 : (2 + C1 / (A * H)) * ((B.filter (fun n : ℕ => ¬ (A ≤ Int.fract (F γ n - j) ∧
        Int.fract (F γ n - j) ≤ 1 - A))).card : ℝ) ≤ (2 + C1) * (2 * (1 + C2) * N * E⁻¹) :=
      mul_le_mul (by linarith) hbad (Nat.cast_nonneg _) (by linarith)
    have : M * N * E⁻¹ = C1 * N * E⁻¹ + 2 * C1 * E⁻¹ * N +
        (2 + C1) * (2 * (1 + C2) * N * E⁻¹) := by rw [hM]; ring
    linarith
  have hlast : M * N * E⁻¹ ≤ (N : ℝ) * E ^ (-(5 / 6 : ℝ)) := by
    have he : E ^ (-(5 / 6 : ℝ)) = E ^ (1 / 6 : ℝ) * E⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hE0]; norm_num
    rw [he]
    have := mul_le_mul_of_nonneg_right hEM (mul_nonneg hNR hEi0)
    linarith [this]
  linarith

end LeanLab.ExceptionalSet.Feed1122ParityCore
