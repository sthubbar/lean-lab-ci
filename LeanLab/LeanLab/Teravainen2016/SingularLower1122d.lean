/-
P0076 J. Teravainen, arXiv 1611.08585, page 30: the lower half of the comparison of the singular
product of Definition 6.1 with `(W/φ(W))^{3/2} Q/|𝒬|`, from display 5.2 and amenability.
This file proves the LEAF `singular_series_lower` of Prop51Split1122b.lean with zero sorry.
Step one, exact: the product over `p ∣ Q W` splits as `Q/|𝒬|` times the product over `p ∣ W`,
by the CRT count of QResCount1122b.lean. Step two: the product over `p ∣ W` is at least an
absolute constant times `(W/φ(W))^{3/2}`, by Mertens in the classes mod 4, here the proved
bias bound built on leaf_mertens_chi4_proved1122d of MertensChi4Tail1122d.lean.
AI wrote the Lean code, Claude, burst-20261122 step singular_series1122d. Goldbach is OPEN.
-/
import LeanLab.Teravainen2016.Prop51Split1122b
import LeanLab.Teravainen2016.MertensChi4Tail1122d
import LeanLab.Teravainen2016.QResCount1122b

open Finset Real
open scoped Classical

namespace LeanLab.Teravainen2016.SingularLower1122d

open LeanLab.Teravainen2016
open LeanLab.Teravainen2016.QResCount1122b

/-- The bias bound leaf_mertens_mod4_bias of MertensMod4Split.lean, page 15, proved by the
Abel summation of MertensMod4Bias.lean from the proved Mertens theorem for chi_4. -/
theorem mertens_mod4_bias_proved1122d : type_of% @leaf_mertens_mod4_bias := by
  obtain ⟨B₀, hB₀, H⟩ := leaf_mertens_chi4_proved1122d
  refine ⟨4 * B₀, by positivity, ?_⟩
  intro y x hy hyx
  set χ : ℕ → ℝ := fun p => if p % 4 = 1 then (1 : ℝ) else if p % 4 = 3 then -1 else 0 with hχ
  set F := (Ioc ⌊y⌋₊ ⌊x⌋₊).filter Nat.Prime
  have heq : ∑ p ∈ F.filter (fun p => p % 4 = 1), (1 : ℝ) / p -
      ∑ p ∈ F.filter (fun p => p % 4 = 3), (1 : ℝ) / p = ∑ p ∈ F, χ p / p := by
    rw [Finset.sum_filter (s := F), Finset.sum_filter (s := F), ← sum_sub_distrib]
    apply sum_congr rfl
    intro p _
    simp only [hχ]
    split_ifs with h1 h3 <;> first | omega | ring
  rw [heq, abel_weighted χ hy hyx]
  have hx2 : 2 ≤ x := hy.trans hyx
  have hl2 : (1 / 2 : ℝ) < log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hly : 1 / 2 < log y := lt_of_lt_of_le hl2 (Real.log_le_log (by norm_num) hy)
  have hlx : 1 / 2 < log x := lt_of_lt_of_le hl2 (Real.log_le_log (by norm_num) hx2)
  have hlyp : 0 < log y := by linarith
  have hlxp : 0 < log x := by linarith
  set Bf : ℝ → ℝ := fun t => ∑ p ∈ Nat.primesLE ⌊t⌋₊, χ p * log p / p with hBf
  let w : ℝ → ℝ := fun t => 1 / (t * log t ^ 2)
  have hwi : IntervalIntegrable w MeasureTheory.volume y x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hyx]
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have hden : t * log t ^ 2 ≠ 0 := mul_ne_zero ht0 (pow_ne_zero 2 hl)
    apply ContinuousAt.continuousWithinAt
    dsimp [w]
    fun_prop (disch := assumption)
  have hint : (∫ t in y..x, w t) = 1 / log y - 1 / log x := by
    have hd : ∀ t ∈ Set.uIcc y x,
        HasDerivAt (fun t : ℝ => -(log t)⁻¹) (w t) t := by
      intro t ht
      rw [Set.uIcc_of_le hyx] at ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have hl : log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
      convert ((Real.hasDerivAt_log ht0).inv hl).neg using 1
      dsimp [w]
      field_simp
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hwi
    simpa only [one_div, neg_sub_neg] using hi
  have hbound : |∫ t in y..x, Bf t / (t * log t ^ 2)| ≤ ∫ t in y..x, B₀ * w t := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume)
      (f := fun t => Bf t / (t * log t ^ 2)) hyx
      (g := fun t => B₀ * w t) (Filter.Eventually.of_forall (fun t ht => by
        have ht2 : 2 ≤ t := le_trans hy ht.1.le
        have hden : 0 < t * log t ^ 2 := by
          have hlog := Real.log_pos (by linarith : 1 < t)
          positivity
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hden]
        have h := H t ht2
        exact (div_le_div_of_nonneg_right h hden.le).trans_eq (by dsimp [w]; ring)))
      (hwi.const_mul B₀)
    exact hb
  rw [intervalIntegral.integral_const_mul, hint] at hbound
  have hBx := H x hx2
  have hBy := H y hy
  have h1 : Bf x / log x ≤ B₀ / log x := by
    rw [div_le_div_iff_of_pos_right hlxp]; exact (le_abs_self _).trans hBx
  have h2 : -(Bf y / log y) ≤ B₀ / log y := by
    rw [← neg_div, div_le_div_iff_of_pos_right hlyp]; exact (neg_le_abs _).trans hBy
  have h3 : (∫ t in y..x, Bf t / (t * log t ^ 2)) ≤ B₀ * (1 / log y - 1 / log x) :=
    (le_abs_self _).trans hbound
  have hiy : 1 / log y ≤ 2 := by rw [div_le_iff₀ hlyp]; linarith
  have hmain : Bf x / log x - Bf y / log y + ∫ t in y..x, Bf t / (t * log t ^ 2) ≤
      2 * B₀ * (1 / log y) := by
    have : B₀ / log x + B₀ / log y + B₀ * (1 / log y - 1 / log x) = 2 * B₀ * (1 / log y) := by
      ring
    linarith
  calc _ ≤ 2 * B₀ * (1 / log y) := hmain
    _ ≤ 2 * B₀ * 2 := mul_le_mul_of_nonneg_left hiy (by positivity)
    _ = 4 * B₀ := by ring

/-- The local factor of Definition 6.1, page 21, at a prime `p` where `L` has no root of
`L ≡ 0` and, for `p ≡ -1 mod 4`, `p ≠ 3`, none of `L ≡ 1`: the value of `singularLocal`
there, which is the factor of display 5.2. -/
noncomputable def gLoc (p : ℕ) : ℝ :=
  if p % 4 = 3 then (if p = 3 then 1 else (1 - 2 / (p : ℝ))⁻¹) else (1 - 1 / (p : ℝ))⁻¹

theorem singularLocal_eq {K c : ℤ} {p : ℕ} (hp : p.Prime) (hK : (p : ℤ) ∣ K)
    (h0 : ¬ (p : ℤ) ∣ c) (h1 : p % 4 = 3 → p ≠ 3 → ¬ (p : ℤ) ∣ c - 1) :
    singularLocal K c p = gLoc p := by
  have hp1 : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
  have hz : ∀ n : ℕ, ¬ (K * n + c) % (p : ℤ) = 0 := by
    intro n h
    apply h0
    have h3 : (p : ℤ) ∣ K * n + c := Int.dvd_of_emod_eq_zero h
    have h2 : (p : ℤ) ∣ K * n := dvd_mul_of_dvd_left hK _
    exact (dvd_add_right h2).mp h3
  have ho : p % 4 = 3 → p ≠ 3 → ∀ n : ℕ, ¬ (K * n + c) % (p : ℤ) = 1 := by
    intro h4 h3 n h
    apply h1 h4 h3
    have e : (K * n + c - 1) % (p : ℤ) = 0 := by
      rw [Int.sub_emod, h, Int.emod_eq_of_lt (by norm_num) hp1]; simp
    have h5 : (p : ℤ) ∣ K * n + (c - 1) := by
      have := Int.dvd_of_emod_eq_zero e
      rwa [add_sub_assoc] at this
    have h2 : (p : ℤ) ∣ K * n := dvd_mul_of_dvd_left hK _
    exact (dvd_add_right h2).mp h5
  unfold singularLocal gLoc
  split_ifs with h4 h3
  · rfl
  · rw [filter_false_of_mem (fun n _ => by
      rintro (h | h)
      · exact hz n h
      · exact ho h4 h3 n h)]
    simp
  · rw [filter_false_of_mem (fun n _ => hz n)]; simp

/-- Facts on `W`: the natural number `Wn` with `Wn = W`, divisible by `2` and `3`. -/
theorem WW_facts {J w : ℕ} (hJ : 5 ≤ J) :
    ((WW J w).toNat : ℤ) = WW J w ∧ 2 ∣ (WW J w).toNat ∧ 3 ∣ (WW J w).toNat := by
  have hpos := WW_pos' J w
  have e : ((WW J w).toNat : ℤ) = WW J w := Int.toNat_of_nonneg hpos.le
  have h2 : (2 : ℤ) ∣ WW J w := by
    unfold WW Wmod
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _) _
  have h3 : (3 : ℤ) ∣ WW J w := by
    unfold WW Wmod
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (by norm_num) _) _
  refine ⟨e, ?_, ?_⟩
  · have : ((2 : ℕ) : ℤ) ∣ ((WW J w).toNat : ℤ) := by rw [e]; exact_mod_cast h2
    exact Int.natCast_dvd_natCast.mp this
  · have : ((3 : ℕ) : ℤ) ∣ ((WW J w).toNat : ℤ) := by rw [e]; exact_mod_cast h3
    exact Int.natCast_dvd_natCast.mp this

/-- Step one, the Euler product: for `c₀ ∈ 𝒬` every factor of `𝔖(L)` at `p ∣ Q W`
is the factor `gLoc p`, as no `n` has `L(n) ≡ 0` or, where it counts, `L(n) ≡ 1`. -/
theorem singularS_eq_prod {J w : ℕ} (hJ : 5 ≤ J) {b : ℤ} (hb : Amenable (WW J w) b)
    {Q : ℕ} (hQ : 1 ≤ Q) {c₀ : ℕ} (hc : c₀ ∈ QRes Q (WW J w) b) :
    singularS ((Q : ℤ) * WW J w) (WW J w * c₀ + b) =
      ∏ p ∈ (Q * (WW J w).toNat).primeFactors, gLoc p := by
  obtain ⟨e, -, -⟩ := WW_facts (w := w) hJ
  set Wn := (WW J w).toNat with hWn
  unfold singularS
  have hK : ((Q : ℤ) * WW J w).natAbs = Q * Wn := by
    rw [← e]; exact_mod_cast Int.natAbs_natCast (Q * Wn)
  rw [hK]
  refine prod_congr rfl (fun p hp => ?_)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hcop : IsCoprime b (WW J w) := hb.2.2.1
  simp only [QRes, mem_filter, mem_range] at hc
  obtain ⟨-, hc1, hc2⟩ := hc
  have hpZ : (p : ℤ) ∣ (Q : ℤ) * WW J w := by
    rw [← e]; exact_mod_cast hpd
  have hp2 : ¬ (p : ℤ) ∣ 1 := by
    intro h
    have := Int.eq_one_of_dvd_one (by positivity) h
    have := hpp.one_lt; omega
  apply singularLocal_eq hpp hpZ
  · intro h
    rcases (Nat.Prime.dvd_mul hpp).mp hpd with hq | hw
    · exact hp2 (hc1.isUnit_of_dvd' h (by exact_mod_cast hq) |> fun u => by
        rw [Int.isUnit_iff] at u; rcases u with u | u <;> rw [u] <;> simp)
    · have hwZ : (p : ℤ) ∣ WW J w := by rw [← e]; exact_mod_cast hw
      have hbp : (p : ℤ) ∣ b := (dvd_add_right (dvd_mul_of_dvd_left hwZ _)).mp h
      exact hp2 (hcop.isUnit_of_dvd' hbp hwZ |> fun u => by
        rw [Int.isUnit_iff] at u; rcases u with u | u <;> rw [u] <;> simp)
  · intro h4 h3 h
    rcases (Nat.Prime.dvd_mul hpp).mp hpd with hq | hw
    · exact hc2 p hpp h4 h3 hq h
    · have hwZ : (p : ℤ) ∣ WW J w := by rw [← e]; exact_mod_cast hw
      have h' : (p : ℤ) ∣ WW J w * c₀ + (b - 1) := by rwa [add_sub_assoc] at h
      have hbp : (p : ℤ) ∣ b - 1 := (dvd_add_right (dvd_mul_of_dvd_left hwZ _)).mp h'
      exact hb.2.2.2.1 p hpp h4 h3 hwZ hbp

/-- Display 5.2 as a count: `|𝒬| = Q ∏_{p ∣ Q, p ∤ W} (1 - ω(p)/p)`, written with the
inverse local factors, by the CRT count `sieve_count` of QResCount1122b.lean. -/
theorem qres_card_eq {J w : ℕ} (hJ : 5 ≤ J) {b : ℤ} (hb : Amenable (WW J w) b)
    {Q : ℕ} (hQ : 1 ≤ Q) :
    (#(QRes Q (WW J w) b) : ℝ) =
      Q * ∏ p ∈ Q.primeFactors, (if p ∣ (WW J w).toNat then 1 else gLoc p)⁻¹ := by
  obtain ⟨e, h2, h3⟩ := WW_facts (w := w) hJ
  set Wn := (WW J w).toNat with hWn
  have hcop : IsCoprime b (WW J w) := hb.2.2.1
  have key := sieve_count (Loc (WW J w) b) Q
  rw [← qres_eq_filter Q (by omega)] at key
  have hloc : ∀ p ∈ Q.primeFactors, (#((range p).filter (Loc (WW J w) b p)) : ℝ) =
      p * (if p ∣ Wn then 1 else gLoc p)⁻¹ := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    by_cases hw : p ∣ Wn
    · have hwZ : (p : ℤ) ∣ WW J w := by rw [← e]; exact_mod_cast hw
      rw [if_pos hw, inv_one, mul_one]
      have : (range p).filter (Loc (WW J w) b p) = range p := by
        refine filter_true_of_mem (fun r _ => ⟨fun h => ?_, fun h4 h3' h => ?_⟩)
        · have hbp : (p : ℤ) ∣ b := (dvd_add_right (dvd_mul_of_dvd_left hwZ _)).mp h
          have u := hcop.isUnit_of_dvd' hbp hwZ
          rw [Int.isUnit_iff] at u
          have := hpp.one_lt
          rcases u with u | u <;> omega
        · have h' : (p : ℤ) ∣ WW J w * r + (b - 1) := by rwa [add_sub_assoc] at h
          exact hb.2.2.2.1 p hpp h4 h3' hwZ ((dvd_add_right (dvd_mul_of_dvd_left hwZ _)).mp h')
      rw [this, card_range]
    · haveI : Fact p.Prime := ⟨hpp⟩
      have hwZ : ¬ (p : ℤ) ∣ WW J w := by
        intro h; apply hw; rw [← e] at h; exact_mod_cast h
      rw [loc_count p _ b hwZ, if_neg hw]
      have hp2 : p ≠ 2 := by rintro rfl; exact hw h2
      have hp3 : p ≠ 3 := by rintro rfl; exact hw h3
      have hp5 : 5 ≤ p := by
        have := hpp.two_le
        rcases Nat.lt_or_ge p 5 with h | h
        · interval_cases p <;> simp_all <;> exact absurd hpp (by decide)
        · exact h
      have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp5
      unfold gLoc
      by_cases h4 : p % 4 = 3
      · rw [if_pos ⟨h4, hp3⟩, if_pos h4, if_neg hp3, inv_inv, Nat.cast_sub (by omega)]
        field_simp
        norm_num
      · rw [if_neg (fun h => h4 h.1), if_neg h4, inv_inv, Nat.cast_sub (by omega)]
        field_simp
        norm_num
  have key' := congrArg (Nat.cast : ℕ → ℝ) key
  push_cast at key'
  rw [prod_congr rfl hloc, prod_mul_distrib] at key'
  have hB : (∏ p ∈ Q.primeFactors, (p : ℝ)) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun p hp => by
      have := (Nat.prime_of_mem_primeFactors hp).pos; positivity)
  apply mul_right_cancel₀ hB
  rw [key']; ring

/-- Page 30: `𝔖(L) = (Q/|𝒬|) ∏_{p ∣ W} gLoc p`, from display 5.2 and the Euler product. -/
theorem singularS_factor {J w : ℕ} (hJ : 5 ≤ J) {b : ℤ} (hb : Amenable (WW J w) b)
    {Q : ℕ} (hQ : 1 ≤ Q) {c₀ : ℕ} (hc : c₀ ∈ QRes Q (WW J w) b) :
    singularS ((Q : ℤ) * WW J w) (WW J w * c₀ + b) =
      (Q : ℝ) / #(QRes Q (WW J w) b) * ∏ p ∈ (WW J w).toNat.primeFactors, gLoc p := by
  rw [singularS_eq_prod hJ hb hQ hc, qres_card_eq hJ hb hQ]
  obtain ⟨e, -, -⟩ := WW_facts (w := w) hJ
  set Wn := (WW J w).toNat with hWn
  have hWn0 : Wn ≠ 0 := by
    intro h; have := WW_pos' J w; rw [← e, h] at this; simp at this
  have hQ0 : (Q : ℝ) ≠ 0 := by
    have : (0 : ℝ) < Q := by exact_mod_cast hQ
    exact this.ne'
  rw [prod_inv_distrib, div_mul_eq_div_div, div_self hQ0, one_div, inv_inv]
  have hf : ∏ p ∈ Q.primeFactors, (if p ∣ Wn then 1 else gLoc p) =
      ∏ p ∈ Q.primeFactors.filter (fun p => ¬ p ∣ Wn), gLoc p := by
    rw [prod_filter]
    refine prod_congr rfl (fun p _ => ?_)
    by_cases h : p ∣ Wn <;> simp [h]
  rw [hf, ← prod_union]
  · congr 1
    ext p
    simp only [mem_union, mem_filter, Nat.primeFactors_mul (by omega : Q ≠ 0) hWn0]
    constructor
    · rintro (h | h)
      · by_cases hd : p ∣ Wn
        · exact Or.inr (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors h, hd, hWn0⟩)
        · exact Or.inl ⟨h, hd⟩
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h.1
      · exact Or.inr h
  · rw [disjoint_left]
    intro p hp hp'
    exact (mem_filter.mp hp).2 (Nat.dvd_of_mem_primeFactors hp')

/-- The primes dividing `W` of display 3.3 are `2`, `3` and `5 ≤ p ≤ w`. -/
theorem WW_primeFactors {J w : ℕ} (hJ : 5 ≤ J) :
    (WW J w).toNat.primeFactors = insert 2 (insert 3 (Sw w)) := by
  obtain ⟨e, h2, h3⟩ := WW_facts (w := w) hJ
  have hWn0 : (WW J w).toNat ≠ 0 := by
    intro h; have := WW_pos' J w; rw [← e, h] at this; simp at this
  ext p
  rw [Nat.mem_primeFactors]
  simp only [mem_insert]
  constructor
  · rintro ⟨hp, hd, -⟩
    have hdZ : (p : ℤ) ∣ Wmod J (Sw w) := by
      have : ((p : ℕ) : ℤ) ∣ ((WW J w).toNat : ℤ) := by exact_mod_cast hd
      rw [e] at this; exact this
    exact prime_dvd_Wmod (fun q hq => (Sw_spec w q hq).1) hp hdZ
  · rintro (rfl | rfl | h)
    · exact ⟨Nat.prime_two, h2, hWn0⟩
    · exact ⟨Nat.prime_three, h3, hWn0⟩
    · refine ⟨(Sw_spec w p h).1, ?_, hWn0⟩
      have : (p : ℤ) ∣ WW J w := by
        unfold WW Wmod
        exact dvd_mul_of_dvd_right (dvd_prod_of_mem _ h) _
      rw [← e] at this; exact_mod_cast this

/-- `W/φ(W) = ∏_{p ∣ W} (1 - 1/p)^{-1}`, Euler's product for the totient. -/
theorem W_div_totient {J w : ℕ} (hJ : 5 ≤ J) :
    (WW J w : ℝ) / (Nat.totient (WW J w).toNat : ℝ) =
      ∏ p ∈ (WW J w).toNat.primeFactors, (1 - 1 / (p : ℝ))⁻¹ := by
  obtain ⟨e, -, -⟩ := WW_facts (w := w) hJ
  set Wn := (WW J w).toNat with hWn
  have hW : (WW J w : ℝ) = (Wn : ℝ) := by rw [← e]; rfl
  rw [hW]
  have hWn0 : Wn ≠ 0 := by
    intro h; have := WW_pos' J w; rw [← e, h] at this; simp at this
  have ht := congrArg (Nat.cast : ℕ → ℝ) (Nat.totient_mul_prod_primeFactors Wn)
  push_cast at ht
  have hsub : ∏ p ∈ Wn.primeFactors, (((p - 1 : ℕ) : ℝ)) =
      ∏ p ∈ Wn.primeFactors, ((p : ℝ) - 1) := by
    refine prod_congr rfl (fun p hp => ?_)
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]; simp
  rw [hsub] at ht
  have hφ : (0 : ℝ) < Nat.totient Wn := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hden : ∏ p ∈ Wn.primeFactors, ((p : ℝ) - 1) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun p hp => by
      have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      linarith)
  have hfac : ∏ p ∈ Wn.primeFactors, (1 - 1 / (p : ℝ))⁻¹ =
      (∏ p ∈ Wn.primeFactors, (p : ℝ)) / ∏ p ∈ Wn.primeFactors, ((p : ℝ) - 1) := by
    rw [← prod_div_distrib]
    refine prod_congr rfl (fun p hp => ?_)
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h0 : (p : ℝ) ≠ 0 := by linarith
    field_simp
  rw [hfac, div_eq_div_iff hφ.ne' hden, ← ht]; ring

/-- Telescoping: `∑_{4 < n ≤ w} (1/(n-1) - 1/n) = 1/4 - 1/w`. -/
theorem telescope_Ioc (w : ℕ) (hw : 4 ≤ w) :
    ∑ n ∈ Ioc 4 w, ((1 : ℝ) / ((n : ℝ) - 1) - 1 / n) = 1 / 4 - 1 / w := by
  induction w, hw using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [sum_Ioc_succ_top hn, ih]
    have : (4 : ℝ) ≤ n := by exact_mod_cast hn
    push_cast
    have h1 : (n : ℝ) + 1 - 1 = n := by ring
    rw [h1]
    ring

/-- Mertens in the classes mod 4, page 30: the product of `(1 - 1/p)^{-1}` over `5 ≤ p ≤ w`,
`p ≢ -1 mod 4`, is at most a constant times the same product over `p ≡ -1 mod 4`. -/
theorem mertens_class_ratio : ∃ M : ℝ, 0 < M ∧ ∀ w : ℕ, 4 ≤ w →
    ∏ p ∈ (Sw w).filter (fun p => ¬ p % 4 = 3), (1 - 1 / (p : ℝ))⁻¹ ≤
      M * ∏ p ∈ (Sw w).filter (fun p => p % 4 = 3), (1 - 1 / (p : ℝ))⁻¹ := by
  obtain ⟨B, hB0, HB⟩ := mertens_mod4_bias_proved1122d
  refine ⟨Real.exp (B + 1 / 4), Real.exp_pos _, fun w hw => ?_⟩
  have hSw : Sw w = (Ioc 4 w).filter Nat.Prime := by
    ext p; simp only [Sw, mem_filter, mem_Icc, mem_Ioc]
    constructor <;> rintro ⟨⟨h1, h2⟩, h3⟩ <;> exact ⟨⟨by omega, h2⟩, h3⟩
  have hbias := HB ((4 : ℕ) : ℝ) (w : ℝ) (by norm_num) (by exact_mod_cast hw)
  rw [Nat.floor_natCast, Nat.floor_natCast, ← hSw] at hbias
  set S := Sw w
  have hS5 : ∀ p ∈ S, p.Prime ∧ 5 ≤ p := fun p hp => Sw_spec w p hp
  have hf1 : S.filter (fun p => ¬ p % 4 = 3) = S.filter (fun p => p % 4 = 1) := by
    refine filter_congr (fun p hp => ?_)
    obtain ⟨hpp, hp5⟩ := hS5 p hp
    have ho := Nat.odd_iff.mp (hpp.odd_of_ne_two (by omega))
    omega
  have hpR : ∀ p ∈ S, (5 : ℝ) ≤ p := fun p hp => by exact_mod_cast (hS5 p hp).2
  -- upper bound for the first product
  have hA1 : ∏ p ∈ S.filter (fun p => ¬ p % 4 = 3), (1 - 1 / (p : ℝ))⁻¹ ≤
      Real.exp (∑ p ∈ S.filter (fun p => ¬ p % 4 = 3), (1 : ℝ) / ((p : ℝ) - 1)) := by
    rw [Real.exp_sum]
    refine prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
    · have := hpR p (mem_filter.mp hp).1
      have : 0 < 1 - 1 / (p : ℝ) := by
        rw [sub_pos, div_lt_one (by linarith)]; linarith
      positivity
    · have := hpR p (mem_filter.mp hp).1
      have e : (1 - 1 / (p : ℝ))⁻¹ = 1 / ((p : ℝ) - 1) + 1 := by
        have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
        have h0 : (p : ℝ) ≠ 0 := by linarith
        field_simp
        ring
      rw [e]; exact Real.add_one_le_exp _
  -- lower bound for the second product
  have hA3 : Real.exp (∑ p ∈ S.filter (fun p => p % 4 = 3), (1 : ℝ) / p) ≤
      ∏ p ∈ S.filter (fun p => p % 4 = 3), (1 - 1 / (p : ℝ))⁻¹ := by
    rw [Real.exp_sum]
    refine prod_le_prod₀ (fun p _ => (Real.exp_pos _).le) (fun p hp => ?_)
    have := hpR p (mem_filter.mp hp).1
    exact exp_le_inv_one_sub (by rw [div_lt_one (by linarith)]; linarith)
  -- the sum of 1/(p-1) against the sum of 1/p
  have htel : ∑ p ∈ S.filter (fun p => ¬ p % 4 = 3), ((1 : ℝ) / ((p : ℝ) - 1) - 1 / p) ≤ 1 / 4 := by
    have hsub : S.filter (fun p => ¬ p % 4 = 3) ⊆ Ioc 4 w := by
      intro p hp
      have := (mem_filter.mp hp).1
      rw [hSw] at this
      exact (mem_filter.mp this).1
    refine (sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => ?_)).trans ?_
    · have : (5 : ℝ) ≤ n := by exact_mod_cast (show 5 ≤ n by have := mem_Ioc.mp hn; omega)
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le (by linarith) (by linarith)
    · rw [telescope_Ioc w hw]
      have : (0 : ℝ) ≤ 1 / w := by positivity
      linarith
  have hsum : ∑ p ∈ S.filter (fun p => ¬ p % 4 = 3), (1 : ℝ) / ((p : ℝ) - 1) ≤
      ∑ p ∈ S.filter (fun p => p % 4 = 3), (1 : ℝ) / p + (B + 1 / 4) := by
    have e : ∑ p ∈ S.filter (fun p => ¬ p % 4 = 3), (1 : ℝ) / ((p : ℝ) - 1) =
        ∑ p ∈ S.filter (fun p => ¬ p % 4 = 3), (1 : ℝ) / p +
          ∑ p ∈ S.filter (fun p => ¬ p % 4 = 3), ((1 : ℝ) / ((p : ℝ) - 1) - 1 / p) := by
      rw [← sum_add_distrib]; exact sum_congr rfl (fun p _ => by ring)
    rw [e]
    rw [hf1] at htel ⊢
    linarith
  calc _ ≤ _ := hA1
    _ ≤ Real.exp (∑ p ∈ S.filter (fun p => p % 4 = 3), (1 : ℝ) / p + (B + 1 / 4)) :=
        Real.exp_le_exp.mpr hsum
    _ = Real.exp (B + 1 / 4) * Real.exp (∑ p ∈ S.filter (fun p => p % 4 = 3), (1 : ℝ) / p) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ _ := mul_le_mul_of_nonneg_left hA3 (Real.exp_pos _).le

/-- The LEAF `singular_series_lower` of Prop51Split1122b.lean, page 30, proved: the primes
`p ∣ Q`, `p ∤ W` give exactly `Q/|𝒬|` by display 5.2, and the primes `p ∣ W` give
`2 ∏ (1 - 2/p)^{-1} ∏ (1 - 1/p)^{-1}`, at least an absolute constant times `(W/φ(W))^{3/2}`
by Mertens in the classes mod 4. -/
theorem singular_series_lower_proved : type_of% @singular_series_lower := by
  obtain ⟨M, hM, HM⟩ := mertens_class_ratio
  refine ⟨4 / (3 * (3 * M + 1)), by positivity, ?_⟩
  intro J w hJ hw b hb Q hQ c₀ hc
  have hwBig1 : (10 : ℝ) ≤ wBig := by
    calc (10 : ℝ) = (10 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (Real.one_le_rpow (by norm_num) (by positivity))
  have hw4 : 4 ≤ w := by
    have : (4 : ℝ) ≤ w := by linarith
    exact_mod_cast this
  set S := Sw w with hS
  have hS5 : ∀ p ∈ S, 5 ≤ p := fun p hp => (Sw_spec w p hp).2
  have hpR : ∀ p ∈ S, (5 : ℝ) ≤ p := fun p hp => by exact_mod_cast hS5 p hp
  have h3S : 3 ∉ S := fun h => by have := hS5 3 h; omega
  have h2S : 2 ∉ insert 3 S := by
    rw [mem_insert]; rintro (h | h)
    · omega
    · have := hS5 2 h; omega
  set A1 := ∏ p ∈ S.filter (fun p => ¬ p % 4 = 3), (1 - 1 / (p : ℝ))⁻¹ with hA1
  set A3 := ∏ p ∈ S.filter (fun p => p % 4 = 3), (1 - 1 / (p : ℝ))⁻¹ with hA3
  have hhpos : ∀ p ∈ S, 0 < (1 - 1 / (p : ℝ))⁻¹ := fun p hp => by
    have := hpR p hp
    have : 0 < 1 - 1 / (p : ℝ) := by rw [sub_pos, div_lt_one (by linarith)]; linarith
    positivity
  have hA1pos : 0 < A1 := prod_pos (fun p hp => hhpos p (mem_filter.mp hp).1)
  have hA3pos : 0 < A3 := prod_pos (fun p hp => hhpos p (mem_filter.mp hp).1)
  have hratio : A1 ≤ M * A3 := HM w hw4
  -- the W part of the singular product
  have hG : 2 * A1 * A3 ^ 2 ≤ ∏ p ∈ insert 2 (insert 3 S), gLoc p := by
    rw [prod_insert h2S, prod_insert h3S,
      ← prod_filter_mul_prod_filter_not S (fun p => p % 4 = 3)]
    have g2 : gLoc 2 = 2 := by unfold gLoc; norm_num
    have g3 : gLoc 3 = 1 := by unfold gLoc; norm_num
    have gn : ∏ p ∈ S.filter (fun p => ¬ p % 4 = 3), gLoc p = A1 := by
      refine prod_congr rfl (fun p hp => ?_)
      unfold gLoc; rw [if_neg (mem_filter.mp hp).2]
    have g3' : A3 ^ 2 ≤ ∏ p ∈ S.filter (fun p => p % 4 = 3), gLoc p := by
      rw [hA3, ← prod_pow]
      refine prod_le_prod₀ (fun p hp => by positivity) (fun p hp => ?_)
      obtain ⟨hpS, h4⟩ := mem_filter.mp hp
      have h5 := hpR p hpS
      have hp3 : p ≠ 3 := by have := hS5 p hpS; omega
      unfold gLoc
      rw [if_pos h4, if_neg hp3, inv_pow]
      have hpos : 0 < 1 - 2 / (p : ℝ) := by rw [sub_pos, div_lt_one (by linarith)]; linarith
      refine inv_anti₀ hpos ?_
      have : (1 - 1 / (p : ℝ)) ^ 2 = 1 - 2 / p + (1 / p) ^ 2 := by ring
      rw [this]
      have : 0 ≤ (1 / (p : ℝ)) ^ 2 := by positivity
      linarith
    rw [g2, g3, gn]
    nlinarith
  have hX : ∏ p ∈ insert 2 (insert 3 S), (1 - 1 / (p : ℝ))⁻¹ = 3 * (A3 * A1) := by
    rw [prod_insert h2S, prod_insert h3S,
      ← prod_filter_mul_prod_filter_not S (fun p => p % 4 = 3), ← hA3, ← hA1]
    have e2 : ((1 : ℝ) - 1 / ((2 : ℕ) : ℝ))⁻¹ = 2 := by norm_num
    have e3 : ((1 : ℝ) - 1 / ((3 : ℕ) : ℝ))⁻¹ = 3 / 2 := by norm_num
    rw [e2, e3]; ring
  -- the comparison of the W part with (W/φ(W))^{3/2}
  have hkey : 4 / (3 * (3 * M + 1)) * (3 * (A3 * A1)) ^ ((3 : ℝ) / 2) ≤ 2 * A1 * A3 ^ 2 := by
    have hXpos : 0 < 3 * (A3 * A1) := by positivity
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hXpos, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
    have hsq : Real.sqrt (3 * (A3 * A1)) ≤ (3 * M + 1) / 2 * A3 := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have h1 : 3 * (A3 * A1) ≤ 3 * M * A3 ^ 2 := by nlinarith
      have h2 : 3 * M ≤ ((3 * M + 1) / 2) ^ 2 := by nlinarith [sq_nonneg (3 * M - 1)]
      have h3 : 3 * M * A3 ^ 2 ≤ ((3 * M + 1) / 2) ^ 2 * A3 ^ 2 :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      calc 3 * (A3 * A1) ≤ ((3 * M + 1) / 2) ^ 2 * A3 ^ 2 := h1.trans h3
        _ = ((3 * M + 1) / 2 * A3) ^ 2 := by ring
    calc 4 / (3 * (3 * M + 1)) * (3 * (A3 * A1) * Real.sqrt (3 * (A3 * A1)))
        ≤ 4 / (3 * (3 * M + 1)) * (3 * (A3 * A1) * ((3 * M + 1) / 2 * A3)) := by
          gcongr
      _ = 2 * A1 * A3 ^ 2 := by field_simp; ring
  rw [singularS_factor hJ hb hQ hc, W_div_totient hJ, WW_primeFactors hJ, hX]
  have hR : 0 ≤ (Q : ℝ) / #(QRes Q (WW J w) b) := by positivity
  calc 4 / (3 * (3 * M + 1)) * (3 * (A3 * A1)) ^ ((3 : ℝ) / 2) *
        ((Q : ℝ) / #(QRes Q (WW J w) b))
      ≤ 2 * A1 * A3 ^ 2 * ((Q : ℝ) / #(QRes Q (WW J w) b)) :=
        mul_le_mul_of_nonneg_right hkey hR
    _ ≤ ((Q : ℝ) / #(QRes Q (WW J w) b)) * ∏ p ∈ insert 2 (insert 3 S), gLoc p := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left hG hR

end LeanLab.Teravainen2016.SingularLower1122d

#print axioms LeanLab.Teravainen2016.SingularLower1122d.mertens_mod4_bias_proved1122d
#print axioms LeanLab.Teravainen2016.SingularLower1122d.singularLocal_eq
#print axioms LeanLab.Teravainen2016.SingularLower1122d.WW_facts
#print axioms LeanLab.Teravainen2016.SingularLower1122d.singularS_eq_prod
#print axioms LeanLab.Teravainen2016.SingularLower1122d.qres_card_eq
#print axioms LeanLab.Teravainen2016.SingularLower1122d.singularS_factor
#print axioms LeanLab.Teravainen2016.SingularLower1122d.WW_primeFactors
#print axioms LeanLab.Teravainen2016.SingularLower1122d.W_div_totient
#print axioms LeanLab.Teravainen2016.SingularLower1122d.telescope_Ioc
#print axioms LeanLab.Teravainen2016.SingularLower1122d.mertens_class_ratio
#print axioms LeanLab.Teravainen2016.SingularLower1122d.singular_series_lower_proved
