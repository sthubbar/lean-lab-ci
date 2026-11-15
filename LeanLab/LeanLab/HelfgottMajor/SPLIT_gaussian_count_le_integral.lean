import LeanLab.HelfgottMajor.SPLIT_tail_mass_integral
import LeanLab.PNTPort.DirichletZF.U1482Jensen

/-!
Splitting the Gaussian counting step `Decomp269c.gaussian_count_le_integral` into three
smaller steps.

The step bounds the total Gaussian weight of the zeros of `L(s, χ)` inside the critical
strip above height `T` by the density weighted Gaussian integral `gaussianTailIntegral`.

The split separates

* the zero shift case, where the branch is absent and both sides vanish identically,
* the summability of the Gaussian weights over those zeros at nonzero shift,
* the comparison of the total weight with the density weighted Gaussian integral,

and `gaussian_count_le_integral_split` assembles them. The assembly does no analysis: it
decides the shift, discharges the guard `if δ = 0` in the summand by `if_neg`, and transfers
summability and the total across that identification. Hence each step is one inequality, one
summability statement or one case, all strictly weaker than the assembled statement.

The branch at zero shift is the one place where the two sides must be compared with the
junk-value convention in mind: `gaussianTailIntegral q 0 T` is `0` by its guard and the
summand is `0` as well, so the comparison is `0 ≤ 0` and not an appeal to the integral.
-/

namespace LeanLab.HelfgottMajor.Decomp269c
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp123
open MeasureTheory Filter
open scoped Topology
open LeanLab.PNTPort.DirichletZF (Z Z_pos)
open LeanLab.PNTPort.DirichletZF.U1482 (rw_count_L RW)

set_option maxHeartbeats 800000

/-- LEAF. The zero shift case of the Gaussian counting step: at `δ = 0` every summand of the
series is `0`, so the series is summable with total `0`, and the density weighted Gaussian
integral is `0` by its own guard. This gives the whole statement at zero shift and carries no
height hypothesis, since neither side depends on `T` there. -/
theorem gaussian_count_zero_shift (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hδ : δ = 0) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
          if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
          if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) ≤
      gaussianTailIntegral q δ T := by
  subst hδ
  have hz : (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
        if (0 : ℝ) = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |0|)) ^ 2))
      = fun _ => (0 : ℝ) := by
    funext ρ
    simp
  have hg : gaussianTailIntegral q 0 T = 0 := by
    simp [gaussianTailIntegral]
  rw [hz, hg]
  exact ⟨summable_zero, by simp⟩

/-- A zero of a non-principal `L`-function has multiplicity at least one: `L(·, χ)` is entire
and not identically zero, so the vanishing order at a zero is a positive natural number. -/
private lemma one_le_analyticOrderNatAt_LFunction {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {ρ : ℂ}
    (hρ : DirichletCharacter.LFunction χ ρ = 0) :
    1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ := by
  set f := DirichletCharacter.LFunction χ with hfdef
  have hf : AnalyticOnNhd ℂ f Set.univ := fun z _ =>
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hana : AnalyticAt ℂ f ρ := hf ρ (Set.mem_univ ρ)
  have hne : f 2 ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)
  have htop : analyticOrderAt f ρ ≠ ⊤ := by
    intro h
    have hzero : f =ᶠ[𝓝 ρ] 0 := analyticOrderAt_eq_top.mp h
    have hall := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ ρ) hzero (Set.mem_univ (2 : ℂ))
    exact hne hall
  have h0 : analyticOrderAt f ρ ≠ 0 := hana.analyticOrderAt_ne_zero.mpr hρ
  rw [Nat.one_le_iff_ne_zero]
  intro hc
  apply h0
  rw [← Nat.cast_analyticOrderNatAt htop, hc]
  simp

/-- The Gaussian weight of a height `t` is `exp (-W t²)` with `W = 0.1065 / (π |δ|)²`. -/
private lemma gaussian_weight_eq {δ : ℝ} (t : ℝ) :
    Real.exp (-0.1065 * (|t| / (π * |δ|)) ^ 2)
      = Real.exp (-(0.1065 / (π * |δ|) ^ 2) * t ^ 2) := by
  congr 1
  rw [div_pow, sq_abs]
  field_simp

/-- One shell of the zero set contributes at most the weight of its lower end. -/
private lemma gaussian_weight_le_shell {δ : ℝ} (hδ : δ ≠ 0) {t : ℝ} {n : ℕ}
    (hn : ⌊|t|⌋₊ = n) :
    Real.exp (-0.1065 * (|t| / (π * |δ|)) ^ 2)
      ≤ Real.exp (-(0.1065 / (π * |δ|) ^ 2) * (n : ℝ) ^ 2) := by
  have hd : (0 : ℝ) < |δ| := abs_pos.mpr hδ
  have hnle : (n : ℝ) ≤ |t| := hn ▸ Nat.floor_le (abs_nonneg t)
  have hsq : (n : ℝ) ^ 2 ≤ t ^ 2 := by
    have h2 : (n : ℝ) ^ 2 ≤ |t| ^ 2 := by gcongr
    rwa [sq_abs] at h2
  have hW : (0 : ℝ) < 0.1065 / (π * |δ|) ^ 2 := by positivity
  rw [gaussian_weight_eq, Real.exp_le_exp]
  nlinarith [hsq, hW]

/-- The shell majorant `log (n+5) · exp (-W n²)` is summable for positive `W`. -/
private lemma summable_shell_majorant {W : ℝ} (hW : 0 < W) :
    Summable (fun n : ℕ => Real.log ((n : ℝ) + 5) * Real.exp (-(W * (n : ℝ) ^ 2))) := by
  have hr0 : (0 : ℝ) ≤ Real.exp (-W) := (Real.exp_pos (-W)).le
  have hr1 : Real.exp (-W) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom : Summable (fun n : ℕ => ((n : ℝ) + 5) * Real.exp (-W) ^ n) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ 1 * Real.exp (-W) ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one 1
        (by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-W))]; exact hr1)
    have h2 : Summable (fun n : ℕ => Real.exp (-W) ^ n) :=
      summable_geometric_of_lt_one hr0 hr1
    have h3 := h1.add (h2.mul_left 5)
    simpa [pow_one, add_mul] using h3
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hgeom
  · have h5 : (0 : ℝ) < (n : ℝ) + 5 := by positivity
    exact mul_nonneg (Real.log_nonneg (by linarith)) (Real.exp_pos _).le
  · have hlog : Real.log ((n : ℝ) + 5) ≤ (n : ℝ) + 5 :=
      (Real.log_le_self (by positivity)).trans (by linarith)
    have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · simp [h0]
      · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h0
        nlinarith [sq_nonneg ((n : ℝ) - 1)]
    have hexp : Real.exp (-(W * (n : ℝ) ^ 2)) ≤ Real.exp (-W) ^ n := by
      rw [← Real.exp_nat_mul, Real.exp_le_exp]
      nlinarith [hsq, hW]
    exact mul_le_mul hlog hexp (Real.exp_pos _).le (by positivity)

/-- **Shell count.**  In the right half of the strip, a window of height one holds at most
`log (24 Z q (n+5)²) / log (7/6)` zeros of `L(·, χ)`, for `χ` non-principal. -/
private lemma window_card_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (n : ℕ) (s : Finset ℂ)
    (hs : ∀ ρ ∈ s, DirichletCharacter.LFunction χ ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧
      ⌊|ρ.im|⌋₊ = n) :
    (s.card : ℝ) ≤ 2 * (Real.log (24 * Z * (q : ℝ) * ((n : ℝ) + 5) ^ 2) /
      Real.log (7 / 6)) := by
  classical
  set f := DirichletCharacter.LFunction χ with hfdef
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hZ := Z_pos
  have hden : (0 : ℝ) < Real.log (7 / 6) := Real.log_pos (by norm_num)
  have hkey : ∀ (τ : ℝ), |τ| ≤ (n : ℝ) + 1 / 2 → ∀ t : Finset ℂ,
      (∀ ρ ∈ t, ρ ∈ RW f τ) →
      (t.card : ℝ) ≤ Real.log (24 * Z * (q : ℝ) * ((n : ℝ) + 5) ^ 2) / Real.log (7 / 6) := by
    intro τ _ t ht
    have hcard : (t.card : ℝ) = ∑ ρ ∈ t, (1 : ℝ) := by simp
    rw [hcard]
    have hmul : ∑ ρ ∈ t, (1 : ℝ) ≤ ∑ ρ ∈ t, (analyticOrderNatAt f ρ : ℝ) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      have hz : f ρ = 0 := (ht ρ hρ).1
      exact_mod_cast one_le_analyticOrderNatAt_LFunction χ hχ hz
    have hcount := (rw_count_L (χ := χ) hχ τ).2 t ht
    refine hmul.trans (hcount.trans ?_)
    apply div_le_div_of_nonneg_right _ hden.le
    apply Real.log_le_log (by positivity)
    have hle : |τ| + 4 ≤ (n : ℝ) + 5 := by
      have := abs_le.mp ‹|τ| ≤ (n : ℝ) + 1 / 2›
      linarith [this.2]
    have hbase : (0 : ℝ) ≤ 24 * Z * (q : ℝ) := by positivity
    have hsq : (|τ| + 4) ^ 2 ≤ ((n : ℝ) + 5) ^ 2 := by
      have h1 : (0 : ℝ) ≤ |τ| + 4 := by positivity
      nlinarith [hle, h1]
    exact mul_le_mul_of_nonneg_left hsq hbase
  have hcard : s.card =
      (s.filter (fun ρ => 0 ≤ ρ.im)).card + (s.filter (fun ρ => ¬ 0 ≤ ρ.im)).card :=
    (Finset.card_filter_add_card_filter_not (s := s) (p := fun ρ : ℂ => 0 ≤ ρ.im)).symm
  have hp : ((s.filter (fun ρ => 0 ≤ ρ.im)).card : ℝ) ≤
      Real.log (24 * Z * (q : ℝ) * ((n : ℝ) + 5) ^ 2) / Real.log (7 / 6) := by
    apply hkey (n + 1 / 2)
    · rw [abs_of_nonneg]
      positivity
    · intro ρ hρ
      obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp hρ
      obtain ⟨hz, hre1, hre2, hfl⟩ := hs ρ hs1
      refine ⟨hz, hre1, hre2, ?_⟩
      have a : (n : ℝ) ≤ ρ.im := by
        rw [← abs_of_nonneg hs2]
        exact hfl ▸ Nat.floor_le (abs_nonneg ρ.im)
      have b : ρ.im < (n : ℝ) + 1 := by
        rw [← abs_of_nonneg hs2]
        exact hfl ▸ Nat.lt_floor_add_one |ρ.im|
      rw [abs_le]
      constructor <;> linarith
  have hm : ((s.filter (fun ρ => ¬ 0 ≤ ρ.im)).card : ℝ) ≤
      Real.log (24 * Z * (q : ℝ) * ((n : ℝ) + 5) ^ 2) / Real.log (7 / 6) := by
    apply hkey (-(n + 1 / 2))
    · rw [abs_neg, abs_of_nonneg]
      positivity
    · intro ρ hρ
      obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp hρ
      obtain ⟨hz, hre1, hre2, hfl⟩ := hs ρ hs1
      refine ⟨hz, hre1, hre2, ?_⟩
      have hneg : ρ.im < 0 := not_le.mp hs2
      have habs : |ρ.im| = -ρ.im := abs_of_neg hneg
      have a : (n : ℝ) ≤ -ρ.im := by
        rw [← habs]
        exact hfl ▸ Nat.floor_le (abs_nonneg ρ.im)
      have b : -ρ.im < (n : ℝ) + 1 := by
        rw [← habs]
        exact hfl ▸ Nat.lt_floor_add_one |ρ.im|
      rw [abs_le]
      constructor <;> linarith
  have hsum : (s.card : ℝ) =
      ((s.filter (fun ρ => 0 ≤ ρ.im)).card : ℝ) +
        ((s.filter (fun ρ => ¬ 0 ≤ ρ.im)).card : ℝ) := by
    rw [hcard]
    push_cast
    ring
  rw [hsum]
  linarith

/-- `n ≤ n²` for a natural number, as a real. -/
private lemma nat_cast_le_sq (n : ℕ) : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · simp [h0]
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h0
    nlinarith [sq_nonneg ((n : ℝ) - 1)]

/-- The pure Gaussian `exp (-W n²)` is summable on the natural numbers for `W > 0`. -/
private lemma summable_exp_neg_sq {W : ℝ} (hW : 0 < W) :
    Summable (fun n : ℕ => Real.exp (-(W * (n : ℝ) ^ 2))) := by
  have hr0 : (0 : ℝ) ≤ Real.exp (-W) := (Real.exp_pos (-W)).le
  have hr1 : Real.exp (-W) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_)
    (summable_geometric_of_lt_one hr0 hr1)
  rw [← Real.exp_nat_mul, Real.exp_le_exp]
  nlinarith [nat_cast_le_sq n, hW]

/-- **The right half of the strip is summable.**  For a non-principal character the Gaussian
weights of the zeros of `L(·, χ)` with `1/2 ≤ Re ρ < 1` and `|Im ρ| > T` form a summable
family, because each unit window holds only logarithmically many of them. -/
private lemma right_half_gaussian_summable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (δ T : ℝ) (hδ : δ ≠ 0) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧
        ρ.re < 1 ∧ T < |ρ.im|} =>
      Real.exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) := by
  classical
  set W : ℝ := 0.1065 / (π * |δ|) ^ 2 with hWdef
  have hW : 0 < W := by
    rw [hWdef]
    have hd : (0 : ℝ) < |δ| := abs_pos.mpr hδ
    positivity
  set C : ℝ := 1 / Real.log (7 / 6) with hCdef
  have hC0 : 0 < C := by rw [hCdef]; positivity
  have hlog716 : (0 : ℝ) < Real.log (7 / 6) := Real.log_pos (by norm_num)
  have hBq : (0 : ℝ) < 24 * Z * (q : ℝ) := by
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have := Z_pos
    positivity
  set Bq : ℝ := 24 * Z * (q : ℝ) with hBqdef
  set M : ℕ → ℝ := fun n => (2 * C * |Real.log Bq|) * Real.exp (-(W * (n : ℝ) ^ 2))
      + (4 * C) * (Real.log ((n : ℝ) + 5) * Real.exp (-(W * (n : ℝ) ^ 2))) with hMdef
  have hMsum : Summable M := by
    rw [hMdef]
    exact ((summable_exp_neg_sq hW).mul_left _).add ((summable_shell_majorant hW).mul_left _)
  have hMnn : ∀ n, 0 ≤ M n := by
    intro n
    have h1 : (0 : ℝ) ≤ Real.exp (-(W * (n : ℝ) ^ 2)) := (Real.exp_pos _).le
    have h2 : (0 : ℝ) ≤ Real.log ((n : ℝ) + 5) := Real.log_nonneg (by linarith)
    have h3 : (0 : ℝ) ≤ 2 * C * |Real.log Bq| := by positivity
    have h4 : (0 : ℝ) ≤ 4 * C := by positivity
    rw [hMdef]
    exact add_nonneg (mul_nonneg h3 h1) (mul_nonneg h4 (mul_nonneg h2 h1))
  refine summable_of_sum_le (c := ∑' n, M n) (fun ρ => (Real.exp_pos _).le) ?_
  intro u
  set t : Finset ℂ := u.image Subtype.val with htdef
  have hinj : Set.InjOn (Subtype.val : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} → ℂ) ↑u := Subtype.val_injective.injOn
  have hmap : ∑ ρ ∈ t, Real.exp (-0.1065 * (|ρ.im| / (π * |δ|)) ^ 2)
      = ∑ ρ ∈ u, Real.exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2) := by
    rw [htdef, Finset.sum_image hinj]
  rw [← hmap]
  have hmaps : ∀ ρ ∈ t, ⌊|ρ.im|⌋₊ ∈ t.image (fun ρ : ℂ => ⌊|ρ.im|⌋₊) :=
    fun ρ hρ => Finset.mem_image_of_mem _ hρ
  rw [← Finset.sum_fiberwise_of_maps_to (s := t) (t := t.image (fun ρ : ℂ => ⌊|ρ.im|⌋₊))
    (g := fun ρ : ℂ => ⌊|ρ.im|⌋₊)
    (f := fun ρ : ℂ => Real.exp (-0.1065 * (|ρ.im| / (π * |δ|)) ^ 2)) hmaps]
  have hshell : ∀ n : ℕ,
      (∑ ρ ∈ t.filter (fun ρ : ℂ => ⌊|ρ.im|⌋₊ = n),
          Real.exp (-0.1065 * (|ρ.im| / (π * |δ|)) ^ 2)) ≤ M n := by
    intro n
    have hzeros : ∀ ρ ∈ t.filter (fun ρ : ℂ => ⌊|ρ.im|⌋₊ = n),
        DirichletCharacter.LFunction χ ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ ⌊|ρ.im|⌋₊ = n := by
      intro ρ hρ
      obtain ⟨ht1, ht2⟩ := Finset.mem_filter.mp hρ
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht1
      exact ⟨a.property.1, a.property.2.1, a.property.2.2.1, ht2⟩
    have hcards := window_card_le χ hχ n (t.filter (fun ρ : ℂ => ⌊|ρ.im|⌋₊ = n)) hzeros
    have hstep : ∀ ρ ∈ t.filter (fun ρ : ℂ => ⌊|ρ.im|⌋₊ = n),
        Real.exp (-0.1065 * (|ρ.im| / (π * |δ|)) ^ 2) ≤ Real.exp (-(W * (n : ℝ) ^ 2)) := by
      intro ρ hρ
      have hfl : ⌊|ρ.im|⌋₊ = n := (Finset.mem_filter.mp hρ).2
      have h := gaussian_weight_le_shell hδ hfl
      simpa [hWdef] using h
    have hfirst : (∑ ρ ∈ t.filter (fun ρ : ℂ => ⌊|ρ.im|⌋₊ = n),
        Real.exp (-0.1065 * (|ρ.im| / (π * |δ|)) ^ 2))
        ≤ (t.filter (fun ρ : ℂ => ⌊|ρ.im|⌋₊ = n)).card * Real.exp (-(W * (n : ℝ) ^ 2)) := by
      calc (∑ ρ ∈ t.filter (fun ρ : ℂ => ⌊|ρ.im|⌋₊ = n),
            Real.exp (-0.1065 * (|ρ.im| / (π * |δ|)) ^ 2))
          ≤ ∑ _ρ ∈ t.filter (fun ρ : ℂ => ⌊|ρ.im|⌋₊ = n), Real.exp (-(W * (n : ℝ) ^ 2)) :=
            Finset.sum_le_sum hstep
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hlogsplit : Real.log (Bq * ((n : ℝ) + 5) ^ 2) ≤
        |Real.log Bq| + 2 * Real.log ((n : ℝ) + 5) := by
      have h1 : Real.log (Bq * ((n : ℝ) + 5) ^ 2) = Real.log Bq + 2 * Real.log ((n : ℝ) + 5) := by
        rw [Real.log_mul hBq.ne' (by positivity), Real.log_pow]; push_cast; ring
      have h2 : Real.log Bq ≤ |Real.log Bq| := le_abs_self _
      linarith
    have hcards' : ((t.filter (fun ρ : ℂ => ⌊|ρ.im|⌋₊ = n)).card : ℝ) ≤
        2 * C * |Real.log Bq| + 4 * C * Real.log ((n : ℝ) + 5) := by
      have h1 : Real.log (24 * Z * (q : ℝ) * ((n : ℝ) + 5) ^ 2) ≤
          |Real.log Bq| + 2 * Real.log ((n : ℝ) + 5) := by
        have h := hlogsplit
        rwa [hBqdef] at h
      have h2 : Real.log (24 * Z * (q : ℝ) * ((n : ℝ) + 5) ^ 2) / Real.log (7 / 6)
          = Real.log (24 * Z * (q : ℝ) * ((n : ℝ) + 5) ^ 2) * C := by
        rw [hCdef]
        field_simp
      calc ((t.filter (fun ρ : ℂ => ⌊|ρ.im|⌋₊ = n)).card : ℝ)
          ≤ 2 * (Real.log (24 * Z * (q : ℝ) * ((n : ℝ) + 5) ^ 2) / Real.log (7 / 6)) := hcards
        _ = 2 * C * Real.log (24 * Z * (q : ℝ) * ((n : ℝ) + 5) ^ 2) := by rw [h2]; ring
        _ ≤ 2 * C * (|Real.log Bq| + 2 * Real.log ((n : ℝ) + 5)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2 * C * |Real.log Bq| + 4 * C * Real.log ((n : ℝ) + 5) := by ring
    have hexp : (0 : ℝ) ≤ Real.exp (-(W * (n : ℝ) ^ 2)) := (Real.exp_pos _).le
    refine hfirst.trans ?_
    have h2 : ((t.filter (fun ρ : ℂ => ⌊|ρ.im|⌋₊ = n)).card : ℝ) *
        Real.exp (-(W * (n : ℝ) ^ 2)) ≤
        (2 * C * |Real.log Bq| + 4 * C * Real.log ((n : ℝ) + 5)) *
          Real.exp (-(W * (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_right hcards' hexp
    refine h2.trans (le_of_eq ?_)
    rw [hMdef]
    ring
  calc ∑ n ∈ t.image (fun ρ : ℂ => ⌊|ρ.im|⌋₊),
        (∑ ρ ∈ t.filter (fun ρ : ℂ => ⌊|ρ.im|⌋₊ = n),
          Real.exp (-0.1065 * (|ρ.im| / (π * |δ|)) ^ 2))
      ≤ ∑ n ∈ t.image (fun ρ : ℂ => ⌊|ρ.im|⌋₊), M n := Finset.sum_le_sum fun n _ => hshell n
    _ ≤ ∑' n : ℕ, M n := Summable.sum_le_tsum _ (fun n _ => hMnn n) hMsum

/-! ### Reduction to the primitive character and the functional-equation pairing

`LFunction_changeLevel` writes `L(·, χ)` as `L(·, χ.primitiveCharacter)` times the finite Euler
product `∏_{p | q} (1 - χ*(p) p^{-s})`, whose factors do not vanish on `Re s > 0`; so on the strip
the two zero sets agree.  For a primitive `χ` the functional equation
`completedLFunction_one_sub` then pairs a zero `ρ` of the left half `0 < Re ρ < 1/2` with the zero
`1 - ρ` of `L(·, χ⁻¹)` in the right half, where the Jensen window count of `U1482Jensen` applies,
and `|Im (1 - ρ)| = |Im ρ|` carries the Gaussian weight across. -/

private lemma one_sub_char_mul_cpow_ne_zero {N p : ℕ} (χ : DirichletCharacter ℂ N) (hp : 1 < p)
    {ρ : ℂ} (hρ : 0 < ρ.re) :
    (1 : ℂ) - χ (p : ZMod N) * (p : ℂ) ^ (-ρ) ≠ 0 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hnorm : ‖χ (p : ZMod N) * (p : ℂ) ^ (-ρ)‖ < 1 := by
    have hcast : ((p : ℂ)) = ((p : ℝ) : ℂ) := by push_cast; ring
    have h2 : ‖(p : ℂ) ^ (-ρ)‖ = (p : ℝ) ^ (-ρ).re := by
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hp0]
    have h3 : (p : ℝ) ^ (-ρ).re < 1 := by
      rw [Complex.neg_re]
      have hlt : (1 : ℝ) < (p : ℝ) ^ ρ.re := Real.one_lt_rpow hp1 hρ
      rw [Real.rpow_neg hp0.le]
      exact inv_lt_one_of_one_lt₀ hlt
    calc ‖χ (p : ZMod N) * (p : ℂ) ^ (-ρ)‖
        = ‖χ (p : ZMod N)‖ * ‖(p : ℂ) ^ (-ρ)‖ := norm_mul _ _
      _ ≤ 1 * ((p : ℝ) ^ (-ρ).re) := by
          rw [h2]
          exact mul_le_mul (DirichletCharacter.norm_le_one χ _) le_rfl (by positivity) (by norm_num)
      _ < 1 := by rw [one_mul]; exact h3
  intro h
  have hz : χ (p : ZMod N) * (p : ℂ) ^ (-ρ) = 1 := (sub_eq_zero.mp h).symm
  rw [hz, norm_one] at hnorm
  exact lt_irrefl (1 : ℝ) hnorm

private theorem strip_zero_iff_primitiveCharacter {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    DirichletCharacter.LFunction χ ρ = 0 ↔
      DirichletCharacter.LFunction (χ.primitiveCharacter) ρ = 0 := by
  classical
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at h1; rw [Complex.one_re] at h1; linarith
  have hmain := DirichletCharacter.LFunction_changeLevel (χ := χ.primitiveCharacter)
    χ.conductor_dvd_level (s := ρ) (Or.inr hρ1)
  rw [χ.changeLevel_primitiveCharacter] at hmain
  have hprod : (∏ p ∈ q.primeFactors,
      ((1 : ℂ) - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-ρ))) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun p hp => ?_)
    exact one_sub_char_mul_cpow_ne_zero χ.primitiveCharacter
      (Nat.Prime.one_lt (Nat.prime_of_mem_primeFactors hp)) h0
  rw [hmain, mul_eq_zero]
  exact ⟨fun h => h.resolve_right hprod, fun h => Or.inl h⟩

/-! ### The Gamma factor does not vanish in the strip, and the functional equation pairs the halves -/

private lemma gammaFactor_ne_zero_of_strip {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) : DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos h0
  · rw [h.gammaFactor_def]
    refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
    rw [Complex.add_re, Complex.one_re]; linarith

private lemma completedLFunction_eq_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : DirichletCharacter.LFunction χ s = 0) :
    DirichletCharacter.completedLFunction χ s = 0 := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at h0; rw [Complex.zero_re] at h0; exact lt_irrefl _ h0
  have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)
  have hq : DirichletCharacter.completedLFunction χ s / DirichletCharacter.gammaFactor χ s = 0 := by
    rw [← h, hz]
  rcases div_eq_zero_iff.mp hq with hc | hg
  · exact hc
  · exact absurd hg (gammaFactor_ne_zero_of_strip χ h0 h1)

/-- The functional equation maps a strip zero `ρ` of `L(·,χ)` in the left half to the zero `1 - ρ`
of `L(·,χ⁻¹)` in the right half. -/
private theorem inv_LFunction_one_sub_eq_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprim : DirichletCharacter.IsPrimitive χ) {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1 / 2)
    (hz : DirichletCharacter.LFunction χ ρ = 0) :
    DirichletCharacter.LFunction χ⁻¹ (1 - ρ) = 0 := by
  have hstrip1 : ρ.re < 1 := by linarith
  have hc : DirichletCharacter.completedLFunction χ ρ = 0 :=
    completedLFunction_eq_zero χ h0 hstrip1 hz
  have hprim' : DirichletCharacter.IsPrimitive χ⁻¹ := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hprim
  have hFE := DirichletCharacter.IsPrimitive.completedLFunction_one_sub hprim' (s := ρ)
  rw [inv_inv] at hFE
  have hzero' : DirichletCharacter.completedLFunction χ⁻¹ (1 - ρ) = 0 := by
    rw [hFE, hc, mul_zero]
  have hA : 0 < (1 - ρ).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hs0 : (1 - ρ) ≠ 0 := by
    intro h; rw [h] at hA; rw [Complex.zero_re] at hA; exact lt_irrefl _ hA
  have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - ρ) (Or.inl hs0)
  rw [h, hzero', zero_div]

/-- Left-half summability of the Gaussian weights, transferred from the right half of `χ⁻¹`. -/
private theorem left_half_gaussian_summable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprim : DirichletCharacter.IsPrimitive χ) (δ T : ℝ)
    (hright : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ⁻¹ ρ = 0 ∧
        1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
          Real.exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 / 2 ∧ T < |ρ.im|} =>
          Real.exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) := by
  classical
  have key : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 / 2 ∧ T < |ρ.im|},
      DirichletCharacter.LFunction χ⁻¹ (1 - ρ.val) = 0 ∧ 1 / 2 ≤ (1 - ρ.val).re ∧
      (1 - ρ.val).re < 1 ∧ T < |(1 - ρ.val).im| := by
    intro ρ
    obtain ⟨hz, h0, h1, hT⟩ := ρ.property
    refine ⟨inv_LFunction_one_sub_eq_zero hprim h0 h1 hz, ?_, ?_, ?_⟩
    · rw [Complex.sub_re, Complex.one_re]; linarith
    · rw [Complex.sub_re, Complex.one_re]; linarith
    · rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]; exact hT
  set φ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 / 2 ∧ T < |ρ.im|} →
      {ρ : ℂ // DirichletCharacter.LFunction χ⁻¹ ρ = 0 ∧
        1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} :=
    fun ρ => ⟨1 - ρ.val, key ρ⟩ with hφdef
  have hinj : Function.Injective φ := by
    intro a b hab
    have hab' : (1 : ℂ) - a.val = 1 - b.val := by
      have := congrArg Subtype.val hab
      simpa [hφdef] using this
    exact Subtype.ext (by linear_combination -hab')
  have hcomp := hright.comp_injective hinj
  refine (summable_congr (fun ρ => ?_)).mp hcomp
  have hval : ((φ ρ : _) : ℂ) = 1 - ρ.val := rfl
  have him : ((φ ρ : _) : ℂ).im = -ρ.val.im := by
    rw [hval, Complex.sub_im, Complex.one_im, zero_sub]
  simp only [Function.comp_apply, him, abs_neg]

/-- **Reduction of the strip-zero family to the primitive character.**  On the open strip the zeros of
`L(·,χ)` are exactly the zeros of `L(·,χ.primitiveCharacter)`, so the Gaussian weight family is the
same for the two and its summability transfers. -/
private theorem strip_summable_iff_primitiveCharacter {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (δ T : ℝ) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
          Real.exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) ↔
      Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction (χ.primitiveCharacter) ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
          Real.exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) := by
  classical
  have key : ∀ ρ : ℂ, (DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|) ↔
      (DirichletCharacter.LFunction (χ.primitiveCharacter) ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|) := by
    intro ρ
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(strip_zero_iff_primitiveCharacter χ h2.1 h2.2.1).mp h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(strip_zero_iff_primitiveCharacter χ h2.1 h2.2.1).mpr h1, h2⟩
  constructor
  · intro h
    set φ : {ρ : ℂ // DirichletCharacter.LFunction (χ.primitiveCharacter) ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} →
        {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} :=
      fun ρ => ⟨ρ.val, (key ρ.val).mpr ρ.property⟩ with hφ
    have hinj : Function.Injective φ := by
      intro a b hab
      exact Subtype.ext (by simpa [hφ] using congrArg Subtype.val hab)
    have := h.comp_injective hinj
    refine (summable_congr (fun ρ => ?_)).mp this
    simp only [Function.comp_apply, hφ]
  · intro h
    set ψ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} →
        {ρ : ℂ // DirichletCharacter.LFunction (χ.primitiveCharacter) ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} :=
      fun ρ => ⟨ρ.val, (key ρ.val).mp ρ.property⟩ with hψ
    have hinj : Function.Injective ψ := by
      intro a b hab
      exact Subtype.ext (by simpa [hψ] using congrArg Subtype.val hab)
    have := h.comp_injective hinj
    refine (summable_congr (fun ρ => ?_)).mp this
    simp only [Function.comp_apply, hψ]


/-! ### The `ζ` (principal character) branch, first two lemmas -/

private lemma one_le_analyticOrderNatAt_zeta {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hne : ρ ≠ 1) :
    1 ≤ analyticOrderNatAt riemannZeta ρ := by
  have hf : AnalyticOnNhd ℂ LeanLab.PNTPort.DirichletZF.U1482.gZ Set.univ := fun z _ =>
    LeanLab.PNTPort.DirichletZF.U1482.gZ_analyticAt z
  have hana : AnalyticAt ℂ LeanLab.PNTPort.DirichletZF.U1482.gZ ρ := hf ρ (Set.mem_univ ρ)
  have hne2 : LeanLab.PNTPort.DirichletZF.U1482.gZ 2 ≠ 0 := by
    rw [LeanLab.PNTPort.DirichletZF.U1482.gZ_of_ne (by norm_num)]
    have h := riemannZeta_ne_zero_of_one_lt_re (s := 2) (by norm_num)
    have hone : ((2 : ℂ) - 1) ≠ 0 := by norm_num
    exact mul_ne_zero hone h
  have htop : analyticOrderAt LeanLab.PNTPort.DirichletZF.U1482.gZ ρ ≠ ⊤ := by
    intro h
    have hzero : LeanLab.PNTPort.DirichletZF.U1482.gZ =ᶠ[𝓝 ρ] 0 := analyticOrderAt_eq_top.mp h
    have hall := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ ρ) hzero (Set.mem_univ (2 : ℂ))
    exact hne2 hall
  have hg0 : LeanLab.PNTPort.DirichletZF.U1482.gZ ρ = 0 := by
    rw [LeanLab.PNTPort.DirichletZF.U1482.gZ_of_ne hne, hρ, mul_zero]
  have h0 : analyticOrderAt LeanLab.PNTPort.DirichletZF.U1482.gZ ρ ≠ 0 :=
    hana.analyticOrderAt_ne_zero.mpr hg0
  rw [← LeanLab.PNTPort.DirichletZF.U1482.ord_gZ hne, Nat.one_le_iff_ne_zero]
  intro hc
  apply h0
  rw [← Nat.cast_analyticOrderNatAt htop, hc]
  simp

/-- The functional equation of `ζ`: a left-half strip zero pairs with one in the right half. -/
private lemma zeta_one_sub_eq_zero {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1 / 2)
    (hz : riemannZeta ρ = 0) : riemannZeta (1 - ρ) = 0 := by
  have hs0 : ρ ≠ 0 := by
    intro h; rw [h] at h0; rw [Complex.zero_re] at h0; exact lt_irrefl _ h0
  have hc : completedRiemannZeta ρ = 0 := by
    have h := riemannZeta_def_of_ne_zero hs0
    have hq : completedRiemannZeta ρ / Complex.Gammaℝ ρ = 0 := by rw [← h, hz]
    rcases div_eq_zero_iff.mp hq with h' | h'
    · exact h'
    · exact absurd h' (Complex.Gammaℝ_ne_zero_of_re_pos h0)
  have h1r : (0 : ℝ) < (1 - ρ).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hs0' : (1 - ρ) ≠ 0 := by
    intro h; rw [h] at h1r; rw [Complex.zero_re] at h1r; exact lt_irrefl _ h1r
  rw [riemannZeta_def_of_ne_zero hs0', completedRiemannZeta_one_sub, hc, zero_div]



/-! ### The `ζ` (principal character) branch: window count, right half, left half -/

/-- **Shell count for `ζ`.**  A window of height one in the right half of the strip holds at most
`log (24 Z (n+5)²) / log (7/6)` zeros of `ζ`. -/
private lemma window_card_le_zeta (n : ℕ) (s : Finset ℂ)
    (hs : ∀ ρ ∈ s, riemannZeta ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ ⌊|ρ.im|⌋₊ = n) :
    (s.card : ℝ) ≤ 2 * (Real.log (24 * Z * ((n : ℝ) + 5) ^ 2) / Real.log (7 / 6)) := by
  classical
  have hZ := Z_pos
  have hden : (0 : ℝ) < Real.log (7 / 6) := Real.log_pos (by norm_num)
  have hkey : ∀ (τ : ℝ), |τ| ≤ (n : ℝ) + 1 / 2 → ∀ t : Finset ℂ,
      (∀ ρ ∈ t, ρ ∈ RW riemannZeta τ) →
      (t.card : ℝ) ≤ Real.log (24 * Z * ((n : ℝ) + 5) ^ 2) / Real.log (7 / 6) := by
    intro τ hn t ht
    have hcard : (t.card : ℝ) = ∑ ρ ∈ t, (1 : ℝ) := by simp
    rw [hcard]
    have hmul : ∑ ρ ∈ t, (1 : ℝ) ≤ ∑ ρ ∈ t, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      have hz : riemannZeta ρ = 0 := (ht ρ hρ).1
      have hne : ρ ≠ 1 := by
        intro h
        have h1' : ρ.re < 1 := (ht ρ hρ).2.2.1
        rw [h] at h1'
        rw [Complex.one_re] at h1'
        linarith
      exact_mod_cast one_le_analyticOrderNatAt_zeta hz hne
    have hcount := (LeanLab.PNTPort.DirichletZF.U1482.rw_count_zeta τ).2 t ht
    refine hmul.trans (hcount.trans ?_)
    apply div_le_div_of_nonneg_right _ hden.le
    apply Real.log_le_log (by positivity)
    have hle : |τ| + 4 ≤ (n : ℝ) + 5 := by
      have := abs_le.mp hn
      linarith [this.2]
    have hbase : (0 : ℝ) ≤ 24 * Z := by positivity
    have hsq : (|τ| + 4) ^ 2 ≤ ((n : ℝ) + 5) ^ 2 := by
      have h1 : (0 : ℝ) ≤ |τ| + 4 := by positivity
      nlinarith [hle, h1]
    exact mul_le_mul_of_nonneg_left hsq hbase
  have hcard : s.card =
      (s.filter (fun ρ => 0 ≤ ρ.im)).card + (s.filter (fun ρ => ¬ 0 ≤ ρ.im)).card :=
    (Finset.card_filter_add_card_filter_not (s := s) (p := fun ρ : ℂ => 0 ≤ ρ.im)).symm
  have hp : ((s.filter (fun ρ => 0 ≤ ρ.im)).card : ℝ) ≤
      Real.log (24 * Z * ((n : ℝ) + 5) ^ 2) / Real.log (7 / 6) := by
    apply hkey (n + 1 / 2)
    · rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1 / 2)]
    · intro ρ hρ
      obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp hρ
      obtain ⟨hz, hre1, hre2, hfl⟩ := hs ρ hs1
      refine ⟨hz, hre1, hre2, ?_⟩
      have a : (n : ℝ) ≤ ρ.im := by
        rw [← abs_of_nonneg hs2]
        exact hfl ▸ Nat.floor_le (abs_nonneg ρ.im)
      have b : ρ.im < (n : ℝ) + 1 := by
        rw [← abs_of_nonneg hs2]
        exact hfl ▸ Nat.lt_floor_add_one |ρ.im|
      rw [abs_le]
      constructor <;> linarith
  have hm : ((s.filter (fun ρ => ¬ 0 ≤ ρ.im)).card : ℝ) ≤
      Real.log (24 * Z * ((n : ℝ) + 5) ^ 2) / Real.log (7 / 6) := by
    apply hkey (-(n + 1 / 2))
    · rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1 / 2)]
    · intro ρ hρ
      obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp hρ
      obtain ⟨hz, hre1, hre2, hfl⟩ := hs ρ hs1
      refine ⟨hz, hre1, hre2, ?_⟩
      have hneg : ρ.im < 0 := not_le.mp hs2
      have habs : |ρ.im| = -ρ.im := abs_of_neg hneg
      have a : (n : ℝ) ≤ -ρ.im := by
        rw [← habs]
        exact hfl ▸ Nat.floor_le (abs_nonneg ρ.im)
      have b : -ρ.im < (n : ℝ) + 1 := by
        rw [← habs]
        exact hfl ▸ Nat.lt_floor_add_one |ρ.im|
      rw [abs_le]
      constructor <;> linarith
  have hsum : (s.card : ℝ) =
      ((s.filter (fun ρ => 0 ≤ ρ.im)).card : ℝ) +
        ((s.filter (fun ρ => ¬ 0 ≤ ρ.im)).card : ℝ) := by
    rw [hcard]
    push_cast
    ring
  rw [hsum]
  linarith

private lemma right_half_gaussian_summable_zeta (δ T : ℝ) (hδ : δ ≠ 0) :
    Summable (fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
      Real.exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) := by
  classical
  set W : ℝ := 0.1065 / (π * |δ|) ^ 2 with hWdef
  have hW : 0 < W := by
    rw [hWdef]
    have hd : (0 : ℝ) < |δ| := abs_pos.mpr hδ
    positivity
  set C : ℝ := 1 / Real.log (7 / 6) with hCdef
  have hC0 : 0 < C := by rw [hCdef]; positivity
  have hBq : (0 : ℝ) < 24 * Z := by have := Z_pos; positivity
  set Bq : ℝ := 24 * Z with hBqdef
  set M : ℕ → ℝ := fun n => (2 * C * |Real.log Bq|) * Real.exp (-(W * (n : ℝ) ^ 2))
      + (4 * C) * (Real.log ((n : ℝ) + 5) * Real.exp (-(W * (n : ℝ) ^ 2))) with hMdef
  have hMsum : Summable M := by
    rw [hMdef]
    exact ((summable_exp_neg_sq hW).mul_left _).add ((summable_shell_majorant hW).mul_left _)
  have hMnn : ∀ n, 0 ≤ M n := by
    intro n
    have h1 : (0 : ℝ) ≤ Real.exp (-(W * (n : ℝ) ^ 2)) := (Real.exp_pos _).le
    have h2 : (0 : ℝ) ≤ Real.log ((n : ℝ) + 5) := Real.log_nonneg (by linarith)
    have h3 : (0 : ℝ) ≤ 2 * C * |Real.log Bq| := by positivity
    have h4 : (0 : ℝ) ≤ 4 * C := by positivity
    rw [hMdef]
    exact add_nonneg (mul_nonneg h3 h1) (mul_nonneg h4 (mul_nonneg h2 h1))
  refine summable_of_sum_le (c := ∑' n, M n) (fun ρ => (Real.exp_pos _).le) ?_
  intro u
  set t : Finset ℂ := u.image Subtype.val with htdef
  have hinj : Set.InjOn (Subtype.val : {ρ : ℂ // riemannZeta ρ = 0 ∧
      1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} → ℂ) ↑u := Subtype.val_injective.injOn
  have hmap : ∑ ρ ∈ t, Real.exp (-0.1065 * (|ρ.im| / (π * |δ|)) ^ 2)
      = ∑ ρ ∈ u, Real.exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2) := by
    rw [htdef, Finset.sum_image hinj]
  rw [← hmap]
  have hmaps : ∀ ρ ∈ t, ⌊|ρ.im|⌋₊ ∈ t.image (fun ρ : ℂ => ⌊|ρ.im|⌋₊) :=
    fun ρ hρ => Finset.mem_image_of_mem _ hρ
  rw [← Finset.sum_fiberwise_of_maps_to (s := t) (t := t.image (fun ρ : ℂ => ⌊|ρ.im|⌋₊))
    (g := fun ρ : ℂ => ⌊|ρ.im|⌋₊)
    (f := fun ρ : ℂ => Real.exp (-0.1065 * (|ρ.im| / (π * |δ|)) ^ 2)) hmaps]
  have hshell : ∀ n : ℕ,
      (∑ ρ ∈ t.filter (fun ρ : ℂ => ⌊|ρ.im|⌋₊ = n),
          Real.exp (-0.1065 * (|ρ.im| / (π * |δ|)) ^ 2)) ≤ M n := by
    intro n
    have hzeros : ∀ ρ ∈ t.filter (fun ρ : ℂ => ⌊|ρ.im|⌋₊ = n),
        riemannZeta ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ ⌊|ρ.im|⌋₊ = n := by
      intro ρ hρ
      obtain ⟨ht1, ht2⟩ := Finset.mem_filter.mp hρ
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht1
      exact ⟨a.property.1, a.property.2.1, a.property.2.2.1, ht2⟩
    have hcards := window_card_le_zeta n (t.filter (fun ρ : ℂ => ⌊|ρ.im|⌋₊ = n)) hzeros
    have hstep : ∀ ρ ∈ t.filter (fun ρ : ℂ => ⌊|ρ.im|⌋₊ = n),
        Real.exp (-0.1065 * (|ρ.im| / (π * |δ|)) ^ 2) ≤ Real.exp (-(W * (n : ℝ) ^ 2)) := by
      intro ρ hρ
      have hfl : ⌊|ρ.im|⌋₊ = n := (Finset.mem_filter.mp hρ).2
      have h := gaussian_weight_le_shell hδ hfl
      simpa [hWdef] using h
    have hfirst : (∑ ρ ∈ t.filter (fun ρ : ℂ => ⌊|ρ.im|⌋₊ = n),
        Real.exp (-0.1065 * (|ρ.im| / (π * |δ|)) ^ 2))
        ≤ (t.filter (fun ρ : ℂ => ⌊|ρ.im|⌋₊ = n)).card * Real.exp (-(W * (n : ℝ) ^ 2)) := by
      calc (∑ ρ ∈ t.filter (fun ρ : ℂ => ⌊|ρ.im|⌋₊ = n),
            Real.exp (-0.1065 * (|ρ.im| / (π * |δ|)) ^ 2))
          ≤ ∑ _ρ ∈ t.filter (fun ρ : ℂ => ⌊|ρ.im|⌋₊ = n), Real.exp (-(W * (n : ℝ) ^ 2)) :=
            Finset.sum_le_sum hstep
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hlogsplit : Real.log (Bq * ((n : ℝ) + 5) ^ 2) ≤
        |Real.log Bq| + 2 * Real.log ((n : ℝ) + 5) := by
      have h1 : Real.log (Bq * ((n : ℝ) + 5) ^ 2) = Real.log Bq + 2 * Real.log ((n : ℝ) + 5) := by
        rw [Real.log_mul hBq.ne' (by positivity), Real.log_pow]; push_cast; ring
      have h2 : Real.log Bq ≤ |Real.log Bq| := le_abs_self _
      linarith
    have hcards' : ((t.filter (fun ρ : ℂ => ⌊|ρ.im|⌋₊ = n)).card : ℝ) ≤
        2 * C * |Real.log Bq| + 4 * C * Real.log ((n : ℝ) + 5) := by
      have h1 : Real.log (24 * Z * ((n : ℝ) + 5) ^ 2) ≤
          |Real.log Bq| + 2 * Real.log ((n : ℝ) + 5) := by
        have h := hlogsplit
        rwa [hBqdef] at h
      have h2 : Real.log (24 * Z * ((n : ℝ) + 5) ^ 2) / Real.log (7 / 6)
          = Real.log (24 * Z * ((n : ℝ) + 5) ^ 2) * C := by
        rw [hCdef]; field_simp
      calc ((t.filter (fun ρ : ℂ => ⌊|ρ.im|⌋₊ = n)).card : ℝ)
          ≤ 2 * (Real.log (24 * Z * ((n : ℝ) + 5) ^ 2) / Real.log (7 / 6)) := hcards
        _ = 2 * C * Real.log (24 * Z * ((n : ℝ) + 5) ^ 2) := by rw [h2]; ring
        _ ≤ 2 * C * (|Real.log Bq| + 2 * Real.log ((n : ℝ) + 5)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2 * C * |Real.log Bq| + 4 * C * Real.log ((n : ℝ) + 5) := by ring
    have hexp : (0 : ℝ) ≤ Real.exp (-(W * (n : ℝ) ^ 2)) := (Real.exp_pos _).le
    refine hfirst.trans ?_
    have h2 : ((t.filter (fun ρ : ℂ => ⌊|ρ.im|⌋₊ = n)).card : ℝ) *
        Real.exp (-(W * (n : ℝ) ^ 2)) ≤
        (2 * C * |Real.log Bq| + 4 * C * Real.log ((n : ℝ) + 5)) *
          Real.exp (-(W * (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_right hcards' hexp
    refine h2.trans (le_of_eq ?_)
    rw [hMdef]; ring
  calc ∑ n ∈ t.image (fun ρ : ℂ => ⌊|ρ.im|⌋₊),
        (∑ ρ ∈ t.filter (fun ρ : ℂ => ⌊|ρ.im|⌋₊ = n),
          Real.exp (-0.1065 * (|ρ.im| / (π * |δ|)) ^ 2))
      ≤ ∑ n ∈ t.image (fun ρ : ℂ => ⌊|ρ.im|⌋₊), M n := Finset.sum_le_sum fun n _ => hshell n
    _ ≤ ∑' n : ℕ, M n := Summable.sum_le_tsum _ (fun n _ => hMnn n) hMsum

/-- Left-half summability for `ζ`, transferred from its right half by the functional equation. -/
private theorem left_half_gaussian_summable_zeta (δ T : ℝ)
    (hright : Summable (fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧
        1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
          Real.exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) :
    Summable (fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 / 2 ∧ T < |ρ.im|} =>
          Real.exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) := by
  classical
  have key : ∀ ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 / 2 ∧ T < |ρ.im|},
      riemannZeta (1 - ρ.val) = 0 ∧ 1 / 2 ≤ (1 - ρ.val).re ∧ (1 - ρ.val).re < 1 ∧
        T < |(1 - ρ.val).im| := by
    intro ρ
    obtain ⟨hz, h0, h1, hT⟩ := ρ.property
    refine ⟨zeta_one_sub_eq_zero h0 h1 hz, ?_, ?_, ?_⟩
    · rw [Complex.sub_re, Complex.one_re]; linarith
    · rw [Complex.sub_re, Complex.one_re]; linarith
    · rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]; exact hT
  set φ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 / 2 ∧ T < |ρ.im|} →
      {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} :=
    fun ρ => ⟨1 - ρ.val, key ρ⟩ with hφdef
  have hinj : Function.Injective φ := by
    intro a b hab
    have hab' : (1 : ℂ) - a.val = 1 - b.val := by
      have := congrArg Subtype.val hab
      simpa [hφdef] using this
    exact Subtype.ext (by linear_combination -hab')
  have hcomp := hright.comp_injective hinj
  refine (summable_congr (fun ρ => ?_)).mp hcomp
  have hval : ((φ ρ : _) : ℂ) = 1 - ρ.val := rfl
  have him : ((φ ρ : _) : ℂ).im = -ρ.val.im := by
    rw [hval, Complex.sub_im, Complex.one_im, zero_sub]
  simp only [Function.comp_apply, him, abs_neg]



/-! ### Whole-strip summability from the two halves -/

private theorem summable_strip_of_halves {T : ℝ} {p : ℂ → Prop} {f : ℂ → ℝ}
    (hf0 : ∀ z, 0 ≤ f z)
    (hR : Summable (fun ρ : {ρ : ℂ // p ρ ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
      f ρ.val))
    (hL : Summable (fun ρ : {ρ : ℂ // p ρ ∧ 0 < ρ.re ∧ ρ.re < 1 / 2 ∧ T < |ρ.im|} =>
      f ρ.val)) :
    Summable (fun ρ : {ρ : ℂ // p ρ ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => f ρ.val) := by
  classical
  refine summable_of_sum_le
    (c := (∑' ρ : {ρ : ℂ // p ρ ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|}, f ρ.val)
      + (∑' ρ : {ρ : ℂ // p ρ ∧ 0 < ρ.re ∧ ρ.re < 1 / 2 ∧ T < |ρ.im|}, f ρ.val))
    (fun ρ => hf0 _) ?_
  intro u
  have hsplit : ∑ ρ ∈ u, f ρ.val
      = ∑ ρ ∈ u.filter (fun ρ => 1 / 2 ≤ ρ.val.re), f ρ.val
        + ∑ ρ ∈ u.filter (fun ρ => ¬ 1 / 2 ≤ ρ.val.re), f ρ.val := by
    rw [Finset.sum_filter_add_sum_filter_not (s := u) (p := fun ρ => 1 / 2 ≤ ρ.val.re)]
  rw [hsplit]
  refine add_le_add ?_ ?_
  · set sr : Finset {ρ : ℂ // p ρ ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} :=
      (u.filter (fun ρ => 1 / 2 ≤ ρ.val.re)).attach.image
        (fun ρ : {x // x ∈ u.filter (fun ρ => 1 / 2 ≤ ρ.val.re)} =>
          (⟨ρ.val.val, ρ.val.property.1, (Finset.mem_filter.mp ρ.prop).2,
            ρ.val.property.2.2.1, ρ.val.property.2.2.2⟩ :
              {ρ : ℂ // p ρ ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|})) with hsr
    have hEq : ∑ ρ ∈ u.filter (fun ρ => 1 / 2 ≤ ρ.val.re), f ρ.val
        = ∑ ρ ∈ sr, f ρ.val := by
      rw [hsr, Finset.sum_image]
      · exact (Finset.sum_attach _ (fun y : {ρ : ℂ // p ρ ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => f y.val)).symm
      · intro a _ b _ hab
        exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hab))
    rw [hEq]
    exact Summable.sum_le_tsum _ (fun i _ => hf0 _) hR
  · set sl : Finset {ρ : ℂ // p ρ ∧ 0 < ρ.re ∧ ρ.re < 1 / 2 ∧ T < |ρ.im|} :=
      (u.filter (fun ρ => ¬ 1 / 2 ≤ ρ.val.re)).attach.image
        (fun ρ : {x // x ∈ u.filter (fun ρ => ¬ 1 / 2 ≤ ρ.val.re)} =>
          (⟨ρ.val.val, ρ.val.property.1, ρ.val.property.2.1,
            lt_of_not_ge (Finset.mem_filter.mp ρ.prop).2,
            ρ.val.property.2.2.2⟩ :
              {ρ : ℂ // p ρ ∧ 0 < ρ.re ∧ ρ.re < 1 / 2 ∧ T < |ρ.im|})) with hsl
    have hEq : ∑ ρ ∈ u.filter (fun ρ => ¬ 1 / 2 ≤ ρ.val.re), f ρ.val
        = ∑ ρ ∈ sl, f ρ.val := by
      rw [hsl, Finset.sum_image]
      · exact (Finset.sum_attach _ (fun y : {ρ : ℂ // p ρ ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} => f y.val)).symm
      · intro a _ b _ hab
        exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hab))
    rw [hEq]
    exact Summable.sum_le_tsum _ (fun i _ => hf0 _) hL


/-- The `L`-function of the trivial character mod `1` is `ζ`. -/
private lemma LFunction_one_eq_zeta {m : ℕ} [NeZero m] (hm : m = 1) {s : ℂ} (hs : s ≠ 1) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ m) s = riemannZeta s := by
  subst hm
  have h := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := 1) (s := s) hs
  simpa using h

/-- Summability transfer across a pointwise equivalence of the index predicates. -/
private theorem summable_iff_of_pred_iff {p r : ℂ → Prop} {f : ℂ → ℝ}
    (h : ∀ ρ : ℂ, p ρ ↔ r ρ) :
    Summable (fun ρ : {ρ : ℂ // p ρ} => f ρ.val) ↔
      Summable (fun ρ : {ρ : ℂ // r ρ} => f ρ.val) := by
  classical
  constructor
  · intro hsum
    set φ : {ρ : ℂ // r ρ} → {ρ : ℂ // p ρ} := fun ρ => ⟨ρ.val, (h ρ.val).mpr ρ.property⟩
      with hφ
    have hinj : Function.Injective φ := by
      intro a b hab
      exact Subtype.ext (by simpa [hφ] using congrArg Subtype.val hab)
    have := hsum.comp_injective hinj
    refine (summable_congr (fun ρ => ?_)).mp this
    simp only [Function.comp_apply, hφ]
  · intro hsum
    set ψ : {ρ : ℂ // p ρ} → {ρ : ℂ // r ρ} := fun ρ => ⟨ρ.val, (h ρ.val).mp ρ.property⟩
      with hψ
    have hinj : Function.Injective ψ := by
      intro a b hab
      exact Subtype.ext (by simpa [hψ] using congrArg Subtype.val hab)
    have := hsum.comp_injective hinj
    refine (summable_congr (fun ρ => ?_)).mp this
    simp only [Function.comp_apply, hψ]

set_option maxHeartbeats 4000000 in
/-- LEAF. Summability at nonzero shift: the Gaussian weights of the strip zeros above height
`T` form a summable family. This is the counting input for the branch, with the absolute
convergence coming from the density of the zeros against the Gaussian decay; it says nothing
about the size of the total. -/
theorem gaussian_count_summable (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hδ : δ ≠ 0)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
          exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) := by
  classical
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  rw [strip_summable_iff_primitiveCharacter χ δ T]
  by_cases h1 : χ.primitiveCharacter = 1
  · have hm : χ.conductor = 1 := by
      have hpr := χ.primitiveCharacter_isPrimitive
      rw [h1] at hpr
      rw [← hpr, DirichletCharacter.conductor_one]
    have hζ : ∀ ρ : ℂ, ρ.re < 1 →
        (DirichletCharacter.LFunction χ.primitiveCharacter ρ = 0 ↔ riemannZeta ρ = 0) := by
      intro ρ hρ
      have hne : ρ ≠ 1 := by
        intro h
        rw [h] at hρ
        rw [Complex.one_re] at hρ
        linarith
      rw [h1, LFunction_one_eq_zeta hm hne]
    have hiff : ∀ ρ : ℂ, (DirichletCharacter.LFunction χ.primitiveCharacter ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|) ↔
        (riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|) := by
      intro ρ
      by_cases hB : 0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|
      · have hz := hζ ρ hB.2.1
        constructor
        · rintro ⟨h1', -⟩; exact ⟨hz.mp h1', hB⟩
        · rintro ⟨h1', -⟩; exact ⟨hz.mpr h1', hB⟩
      · refine ⟨fun h => absurd ⟨h.2.1, h.2.2.1, h.2.2.2⟩ hB,
          fun h => absurd ⟨h.2.1, h.2.2.1, h.2.2.2⟩ hB⟩
    have hZ : Summable (fun ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
          Real.exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) :=
      summable_strip_of_halves (p := fun z => riemannZeta z = 0)
        (f := fun z => Real.exp (-0.1065 * (|z.im| / (π * |δ|)) ^ 2))
        (fun z => (Real.exp_pos _).le)
        (right_half_gaussian_summable_zeta δ T hδ)
        (left_half_gaussian_summable_zeta δ T (right_half_gaussian_summable_zeta δ T hδ))
    exact (summable_iff_of_pred_iff (p := fun ρ => DirichletCharacter.LFunction χ.primitiveCharacter ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|)
        (r := fun ρ => riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|)
        (f := fun z => Real.exp (-0.1065 * (|z.im| / (π * |δ|)) ^ 2)) hiff).mpr hZ
  · have hne : χ.primitiveCharacter⁻¹ ≠ 1 := by
      intro h
      exact h1 (by rw [← inv_inv χ.primitiveCharacter, h, inv_one])
    exact summable_strip_of_halves
      (p := fun z => DirichletCharacter.LFunction χ.primitiveCharacter z = 0)
      (f := fun z => Real.exp (-0.1065 * (|z.im| / (π * |δ|)) ^ 2))
      (fun z => (Real.exp_pos _).le)
      (right_half_gaussian_summable (χ := χ.primitiveCharacter) h1 δ T hδ)
      (left_half_gaussian_summable (χ := χ.primitiveCharacter)
        χ.primitiveCharacter_isPrimitive δ T
        (right_half_gaussian_summable (χ := χ.primitiveCharacter⁻¹) hne δ T hδ))

/-- LEAF. The comparison at nonzero shift: the total Gaussian weight of the strip zeros above
height `T` is at most the density weighted Gaussian tail integral. This is the quantitative
half of the branch, and it takes the summability of the weights as a hypothesis so that it is
only the size of the total. -/
theorem gaussian_count_tsum_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hδ : δ ≠ 0)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
          exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2))) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
          exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) ≤
      gaussianTailIntegral q δ T := by
  sorry

/-- The Gaussian counting step, assembled from the three smaller steps. At zero shift the
first step gives the whole statement; at nonzero shift the guard in the summand is discharged
by `if_neg`, which transfers both the summability and the value of the series to the plain
Gaussian weights, and the second and third steps close the two components. -/
theorem gaussian_count_le_integral_split (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
          if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) ∧
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
          if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) ≤
      gaussianTailIntegral q δ T := by
  classical
  by_cases hδ : δ = 0
  · exact gaussian_count_zero_shift q χ δ T hδ
  · have hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|} =>
          exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) :=
      gaussian_count_summable q χ δ T hδ hT
    have hguard : ∀ ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T < |ρ.im|},
        (if δ = 0 then 0 else exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2)) =
          exp (-0.1065 * (|ρ.val.im| / (π * |δ|)) ^ 2) := fun ρ => if_neg hδ
    refine ⟨(summable_congr hguard).mpr hs, ?_⟩
    rw [tsum_congr hguard]
    exact gaussian_count_tsum_le q χ δ T hδ hT hs

end LeanLab.HelfgottMajor.Decomp269c
