/-
P0054 J. Pintz 2021, Section 5, display (5.10): the fourth moment of `f(α) = ∑_{n ≤ N} e(2αn²)`,
`∫₀¹ |f(α)|⁴ dα ≪ N² L^c`, through the count of `n₁² + n₂² = n₃² + n₄²`.
Unit U-1357, PC run 20261021T0604Z-1697, track T2.

* `integral_eq_Q4`: the fourth moment equals the number `Q4 N` of quadruples in `[1,N]⁴`.
* `Q4_le_W`: `Q4 N ≤ N² + 2 W(N, 2N)`, with `W(U,V)` the solutions of `uv = st`,
  `u, s ≤ U`, `v, t ≤ V`, through `(n₁-n₃)(n₁+n₃) = (n₄-n₂)(n₄+n₂)`.
* `W_le`: `W(U,V) ≤ U V H_U²`, `H_U` the harmonic number, by the gcd count of each fibre.
* `display510_proved`: (5.10) with `K₀ = 5`, `c = 2`, for `N ≥ 4`.
* `theorem5_of_noMomentInput`: Theorem 5 CONDITIONAL ON Lemma 1 and the major arc output only.
Binary Goldbach is OPEN. AI-written Lean code, Claude.
-/
import Mathlib
import LeanLab.Pintz2021.Holder511

namespace LeanLab.Pintz2021.Moment510U1357

open Real Finset MeasureTheory
open LeanLab.PNTPort.LargeSieve LeanLab.PNTPort.Gallagher LeanLab.Pintz2021.MinorArcs
open LeanLab.Pintz2021.Holder511

/-- The quadruples `(n₁, n₂, n₃, n₄) ∈ [1,N]⁴` with `n₁² + n₂² = n₃² + n₄²`. -/
def Q4 (N : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((Icc 1 N ×ˢ Icc 1 N) ×ˢ (Icc 1 N ×ˢ Icc 1 N)).filter
    (fun x => x.1.1 ^ 2 + x.1.2 ^ 2 = x.2.1 ^ 2 + x.2.2 ^ 2)

/-- The solutions of `u v = s t` with `u, s ∈ [1,U]`, `v, t ∈ [1,V]`, as `((u,v),(s,t))`. -/
def W (U V : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((Icc 1 U ×ˢ Icc 1 V) ×ˢ (Icc 1 U ×ˢ Icc 1 V)).filter
    (fun y => y.1.1 * y.1.2 = y.2.1 * y.2.2)

/-- The fourth moment of (5.9), (5.10) is the number of quadruples: PROVED. -/
theorem integral_eq_Q4 (N : ℕ) :
    ∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖∑ m ∈ Icc 1 N, e ((2 * m ^ 2 : ℕ) * β)‖ ^ 4 =
      ((Q4 N).card : ℝ) := by
  set k : ℕ → ℕ := fun m => 2 * m ^ 2
  set D : ℕ := 4 * N ^ 2 + 1
  have hD : ∀ m ∈ Icc 1 N, 2 * k m < D := by
    intro m hm
    have := (mem_Icc.mp hm).2
    have : m ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left this 2
    simp only [k, D]; omega
  have hone : ∀ β : ℝ, ∑ m ∈ Icc 1 N, e ((2 * m ^ 2 : ℕ) * β) =
      ∑ m ∈ Icc 1 N, (fun _ => (1 : ℂ)) m * e (k m * β) := by
    intro β; refine sum_congr rfl fun m _ => by simp [k]
  simp_rw [hone]
  rw [fourth_moment _ k D hD]
  simp only [mul_one, sum_const, nsmul_eq_mul, Complex.norm_natCast]
  set s := Icc 1 N
  have hmaps : ∀ x ∈ Q4 N, k x.1.1 + k x.1.2 ∈ range D := by
    intro x hx
    simp only [Q4, mem_filter, mem_product] at hx
    have h1 := hD _ hx.1.1.1; have h2 := hD _ hx.1.1.2
    rw [mem_range]; omega
  rw [card_eq_sum_card_fiberwise hmaps]
  push_cast
  refine sum_congr rfl fun j _ => ?_
  rw [sq, ← Nat.cast_mul, ← card_product, Nat.cast_inj]
  congr 1
  ext x
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := x
  simp only [Q4, k, s, mem_filter, mem_product]
  constructor
  · intro h
    obtain ⟨⟨h1, hj⟩, h2, hj'⟩ := h
    exact ⟨⟨⟨h1, h2⟩, by omega⟩, by omega⟩
  · intro h
    obtain ⟨⟨h1, hq⟩, hj⟩ := h
    exact ⟨⟨h1.1, by omega⟩, h1.2, by omega⟩

/-- HELPER: the diagonal `n₁ = n₃` has at most `N²` quadruples. -/
theorem card_diag_le (N : ℕ) : ((Q4 N).filter (fun x => x.1.1 = x.2.1)).card ≤ N ^ 2 := by
  have h : ((Q4 N).filter (fun x => x.1.1 = x.2.1)).card ≤ (Icc 1 N ×ˢ Icc 1 N).card := by
    refine card_le_card_of_injOn (fun x => x.1) ?_ ?_
    · intro x hx
      rw [mem_coe, mem_filter] at hx
      rw [mem_coe]
      exact (mem_product.mp (mem_filter.mp hx.1).1).1
    · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hx ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ hx' heq
      rw [mem_coe, mem_filter] at hx hx'
      obtain ⟨hx1, hac⟩ := hx
      obtain ⟨hx1', hac'⟩ := hx'
      have hq := (mem_filter.mp hx1).2
      have hq' := (mem_filter.mp hx1').2
      simp only [Prod.mk.injEq] at heq hq hq' hac hac' ⊢
      obtain ⟨rfl, rfl⟩ := heq
      subst hac hac'
      have hd : d ^ 2 = b ^ 2 := by omega
      have hd' : d' ^ 2 = b ^ 2 := by omega
      have hd2 : d = b := Nat.pow_left_injective (n := 2) (by norm_num) hd
      have hd3 : d' = b := Nat.pow_left_injective (n := 2) (by norm_num) hd'
      exact ⟨⟨rfl, rfl⟩, rfl, by rw [hd2, hd3]⟩
  simpa [card_product, sq] using h

/-- HELPER: the part `n₃ < n₁` injects into `W(N, 2N)`. -/
theorem card_lt_le (N : ℕ) :
    ((Q4 N).filter (fun x => x.2.1 < x.1.1)).card ≤ (W N (2 * N)).card := by
  refine card_le_card_of_injOn
    (fun x => ((x.1.1 - x.2.1, x.1.1 + x.2.1), (x.2.2 - x.1.2, x.2.2 + x.1.2))) ?_ ?_
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hx
    simp only [Q4, W, mem_filter, mem_product, mem_Icc, coe_filter, Set.mem_ofPred_eq] at hx ⊢
    obtain ⟨⟨⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, ⟨hc1, hc2⟩, hd1, hd2⟩, hq⟩, hca⟩ := hx
    have hsq : c ^ 2 < a ^ 2 := Nat.pow_lt_pow_left hca (by norm_num)
    have hbd2 : b ^ 2 < d ^ 2 := by omega
    have hbd : b < d := (Nat.pow_lt_pow_iff_left (n := 2) (by norm_num)).mp hbd2
    refine ⟨⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, ⟨by omega, by omega⟩, by omega,
      by omega⟩, ?_⟩
    zify [hca.le, hbd.le]
    have hq' : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (c : ℤ) ^ 2 + (d : ℤ) ^ 2 := by exact_mod_cast hq
    linear_combination hq'
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hx ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ hx' heq
    simp only [Q4, mem_filter, coe_filter, Set.mem_ofPred_eq] at hx hx'
    have hsq : c ^ 2 < a ^ 2 := Nat.pow_lt_pow_left hx.2 (by norm_num)
    have hbd : b < d := (Nat.pow_lt_pow_iff_left (n := 2) (by norm_num)).mp (by omega)
    have hsq' : c' ^ 2 < a' ^ 2 := Nat.pow_lt_pow_left hx'.2 (by norm_num)
    have hbd' : b' < d' := (Nat.pow_lt_pow_iff_left (n := 2) (by norm_num)).mp (by omega)
    simp only [Prod.mk.injEq] at heq ⊢
    have := hx.2; have := hx'.2
    omega

/-- HELPER: the part `n₁ < n₃` injects into `W(N, 2N)`. -/
theorem card_gt_le (N : ℕ) :
    ((Q4 N).filter (fun x => x.1.1 < x.2.1)).card ≤ (W N (2 * N)).card := by
  refine card_le_card_of_injOn
    (fun x => ((x.2.1 - x.1.1, x.2.1 + x.1.1), (x.1.2 - x.2.2, x.1.2 + x.2.2))) ?_ ?_
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hx
    simp only [Q4, W, mem_filter, mem_product, mem_Icc, coe_filter, Set.mem_ofPred_eq] at hx ⊢
    obtain ⟨⟨⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, ⟨hc1, hc2⟩, hd1, hd2⟩, hq⟩, hac⟩ := hx
    have hsq : a ^ 2 < c ^ 2 := Nat.pow_lt_pow_left hac (by norm_num)
    have hdb2 : d ^ 2 < b ^ 2 := by omega
    have hdb : d < b := (Nat.pow_lt_pow_iff_left (n := 2) (by norm_num)).mp hdb2
    refine ⟨⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, ⟨by omega, by omega⟩, by omega,
      by omega⟩, ?_⟩
    zify [hac.le, hdb.le]
    have hq' : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (c : ℤ) ^ 2 + (d : ℤ) ^ 2 := by exact_mod_cast hq
    linear_combination -hq'
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hx ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ hx' heq
    simp only [Q4, mem_filter, coe_filter, Set.mem_ofPred_eq] at hx hx'
    have hsq : a ^ 2 < c ^ 2 := Nat.pow_lt_pow_left hx.2 (by norm_num)
    have hdb : d < b := (Nat.pow_lt_pow_iff_left (n := 2) (by norm_num)).mp (by omega)
    have hsq' : a' ^ 2 < c' ^ 2 := Nat.pow_lt_pow_left hx'.2 (by norm_num)
    have hdb' : d' < b' := (Nat.pow_lt_pow_iff_left (n := 2) (by norm_num)).mp (by omega)
    simp only [Prod.mk.injEq] at heq ⊢
    have := hx.2; have := hx'.2
    omega

/-- `Q4 N ≤ N² + 2 W(N, 2N)`: PROVED. -/
theorem Q4_le_W (N : ℕ) : (Q4 N).card ≤ N ^ 2 + 2 * (W N (2 * N)).card := by
  have h1 := card_filter_add_card_filter_not (s := Q4 N) (fun x => x.1.1 = x.2.1)
  have h2 := card_filter_add_card_filter_not
    (s := (Q4 N).filter (fun x => ¬ x.1.1 = x.2.1)) (fun x => x.2.1 < x.1.1)
  have h3 : ((Q4 N).filter (fun x => ¬ x.1.1 = x.2.1)).filter (fun x => ¬ x.2.1 < x.1.1) ⊆
      (Q4 N).filter (fun x => x.1.1 < x.2.1) := by
    intro x hx
    simp only [mem_filter] at hx ⊢
    exact ⟨hx.1.1, by omega⟩
  have h4 : ((Q4 N).filter (fun x => ¬ x.1.1 = x.2.1)).filter (fun x => x.2.1 < x.1.1) ⊆
      (Q4 N).filter (fun x => x.2.1 < x.1.1) := by
    intro x hx
    simp only [mem_filter] at hx ⊢
    exact ⟨hx.1.1, hx.2⟩
  have := card_le_card h3
  have := card_le_card h4
  have := card_diag_le N
  have := card_lt_le N
  have := card_gt_le N
  omega

/-- HELPER: one fibre of `W`: for fixed `u, s ≥ 1`, the `(v,t) ∈ [1,V]²` with `uv = st` number
at most `⌊V / (s / gcd(s,u))⌋`. -/
theorem fibre_le (U V u s : ℕ) (hs : 1 ≤ s) :
    ((W U V).filter (fun y => (y.1.1, y.2.1) = (u, s))).card ≤ V / (s / Nat.gcd s u) := by
  set g := Nat.gcd s u
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  rw [← Nat.Ioc_filter_dvd_card_eq_div, ← Applications.Icc_one_eq_Ioc]
  refine card_le_card_of_injOn (fun y => y.1.2) ?_ ?_
  · rintro ⟨⟨u', v⟩, ⟨s', t⟩⟩ hy
    simp only [W, mem_filter, mem_product, mem_Icc, coe_filter, Set.mem_ofPred_eq,
      Prod.mk.injEq] at hy ⊢
    obtain ⟨⟨⟨⟨⟨hu1, hu2⟩, hv1, hv2⟩, _, _⟩, heq⟩, rfl, rfl⟩ := hy
    refine ⟨⟨hv1, hv2⟩, ?_⟩
    have hdvd : s' ∣ u' * v := ⟨t, heq⟩
    have hcop : Nat.Coprime (s' / g) (u' / g) := Nat.coprime_div_gcd_div_gcd hg
    have hs' : s' = g * (s' / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left s' u')).symm
    have hu' : u' = g * (u' / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right s' u')).symm
    have h2 : g * (s' / g) ∣ g * ((u' / g) * v) := by
      rw [← hs', ← mul_assoc, ← hu']; exact hdvd
    have h3 : s' / g ∣ (u' / g) * v := Nat.dvd_of_mul_dvd_mul_left hg h2
    rw [mul_comm] at h3
    exact hcop.dvd_of_dvd_mul_right h3
  · intro y hy y' hy' heq
    rw [mem_coe, mem_filter] at hy hy'
    obtain ⟨hyW, hyus⟩ := hy
    obtain ⟨hyW', hyus'⟩ := hy'
    have e1 := (mem_filter.mp hyW).2
    have e2 := (mem_filter.mp hyW').2
    obtain ⟨⟨u1, v1⟩, ⟨s1, t1⟩⟩ := y
    obtain ⟨⟨u2, v2⟩, ⟨s2, t2⟩⟩ := y'
    simp only [Prod.mk.injEq] at hyus hyus' heq e1 e2 ⊢
    obtain ⟨hu1, hs1'⟩ := hyus
    obtain ⟨hu2, hs2'⟩ := hyus'
    subst hu1 hs1' hu2 hs2' heq
    exact ⟨⟨rfl, rfl⟩, rfl, Nat.eq_of_mul_eq_mul_left (by omega) (e1.symm.trans e2)⟩

/-- HELPER: `∑_{e ≤ U} 1/e ≤ 1 + log U`. -/
theorem harm_le (U : ℕ) : ∑ e ∈ Icc 1 U, ((e : ℝ))⁻¹ ≤ 1 + Real.log U := by
  have := harmonic_le_one_add_log U
  simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at this
  exact this

/-- HELPER: `∑_{s ≤ U, d ∣ s} d/s ≤ H_U`. -/
theorem sum_multiples_le (U d : ℕ) (hd : 1 ≤ d) :
    ∑ s ∈ Icc 1 U, (if d ∣ s then (d : ℝ) / s else 0) ≤ ∑ e ∈ Icc 1 U, ((e : ℝ))⁻¹ := by
  rw [← sum_filter]
  have hinj : ∀ x ∈ (Icc 1 U).filter (d ∣ ·), ∀ y ∈ (Icc 1 U).filter (d ∣ ·),
      x / d = y / d → x = y := by
    intro x hx y hy hxy
    have hx' := (mem_filter.mp hx).2; have hy' := (mem_filter.mp hy).2
    rw [← Nat.mul_div_cancel' hx', ← Nat.mul_div_cancel' hy', hxy]
  have heq : ∑ s ∈ (Icc 1 U).filter (d ∣ ·), (d : ℝ) / s =
      ∑ e ∈ ((Icc 1 U).filter (d ∣ ·)).image (· / d), ((e : ℝ))⁻¹ := by
    rw [sum_image hinj]
    refine sum_congr rfl fun s hs => ?_
    have hds := (mem_filter.mp hs).2
    rw [Nat.cast_div hds (by exact_mod_cast (by omega : d ≠ 0)), inv_div]
  rw [heq]
  apply sum_le_sum_of_subset_of_nonneg
  · intro e he
    obtain ⟨s, hs, rfl⟩ := mem_image.mp he
    obtain ⟨hs1, hds⟩ := mem_filter.mp hs
    rw [mem_Icc] at hs1 ⊢
    constructor
    · exact (Nat.le_div_iff_mul_le (by omega)).mpr (by
        obtain ⟨q, rfl⟩ := hds
        have : 1 ≤ q := by
          rcases Nat.eq_zero_or_pos q with h | h
          · subst h; omega
          · exact h
        nlinarith)
    · exact (Nat.div_le_self _ _).trans hs1.2
  · intro _ _ _; positivity

/-- HELPER: `∑_{u, s ≤ U} gcd(s,u)/s ≤ U H_U²`. -/
theorem gcd_sum_le (U : ℕ) :
    ∑ u ∈ Icc 1 U, ∑ s ∈ Icc 1 U, ((Nat.gcd s u : ℕ) : ℝ) / s ≤
      U * (∑ e ∈ Icc 1 U, ((e : ℝ))⁻¹) ^ 2 := by
  set I := Icc 1 U
  set Hs := ∑ e ∈ I, ((e : ℝ))⁻¹
  have hpt : ∀ u ∈ I, ∀ s ∈ I, ((Nat.gcd s u : ℕ) : ℝ) / s ≤
      ∑ d ∈ I, (if d ∣ u then (1 : ℝ) else 0) * (if d ∣ s then (d : ℝ) / s else 0) := by
    intro u hu s hs
    have hu1 := (mem_Icc.mp hu); have hs1 := (mem_Icc.mp hs)
    have hgI : Nat.gcd s u ∈ I := by
      rw [mem_Icc]
      exact ⟨Nat.gcd_pos_of_pos_left _ (by omega),
        (Nat.gcd_le_left _ (by omega)).trans hs1.2⟩
    have := single_le_sum (f := fun d => (if d ∣ u then (1 : ℝ) else 0) *
      (if d ∣ s then (d : ℝ) / s else 0)) (fun d _ => by
        by_cases h1 : d ∣ u <;> by_cases h2 : d ∣ s <;> simp [h1, h2]; positivity) hgI
    simpa [Nat.gcd_dvd_right, Nat.gcd_dvd_left] using this
  calc ∑ u ∈ I, ∑ s ∈ I, ((Nat.gcd s u : ℕ) : ℝ) / s
      ≤ ∑ u ∈ I, ∑ s ∈ I, ∑ d ∈ I,
          (if d ∣ u then (1 : ℝ) else 0) * (if d ∣ s then (d : ℝ) / s else 0) :=
        sum_le_sum fun u hu => sum_le_sum fun s hs => hpt u hu s hs
    _ = ∑ d ∈ I, (∑ u ∈ I, (if d ∣ u then (1 : ℝ) else 0)) *
          (∑ s ∈ I, (if d ∣ s then (d : ℝ) / s else 0)) := by
        calc ∑ u ∈ I, ∑ s ∈ I, ∑ d ∈ I,
              (if d ∣ u then (1 : ℝ) else 0) * (if d ∣ s then (d : ℝ) / s else 0)
            = ∑ u ∈ I, ∑ d ∈ I, ∑ s ∈ I,
              (if d ∣ u then (1 : ℝ) else 0) * (if d ∣ s then (d : ℝ) / s else 0) :=
              sum_congr rfl fun u _ => sum_comm
          _ = ∑ d ∈ I, ∑ u ∈ I, ∑ s ∈ I,
              (if d ∣ u then (1 : ℝ) else 0) * (if d ∣ s then (d : ℝ) / s else 0) := sum_comm
          _ = _ := sum_congr rfl fun d _ => by rw [sum_mul_sum]
    _ ≤ ∑ d ∈ I, ((U : ℝ) / d) * Hs := by
        refine sum_le_sum fun d hd => ?_
        have hd1 := (mem_Icc.mp hd).1
        have hc : ∑ u ∈ I, (if d ∣ u then (1 : ℝ) else 0) ≤ (U : ℝ) / d := by
          rw [sum_boole]
          have : ((I.filter (d ∣ ·)).card : ℝ) = ((U / d : ℕ) : ℝ) := by
            congr 1
            simp only [I]
            rw [Applications.Icc_one_eq_Ioc]; exact Nat.Ioc_filter_dvd_card_eq_div U d
          rw [this]; exact Nat.cast_div_le
        apply mul_le_mul hc (sum_multiples_le U d hd1)
        · exact sum_nonneg fun s _ => by split_ifs <;> positivity
        · positivity
    _ = U * Hs ^ 2 := by
        rw [← sum_mul]
        have : ∑ d ∈ I, (U : ℝ) / d = U * Hs := by
          rw [mul_sum]; refine sum_congr rfl fun d _ => by rw [div_eq_mul_inv]
        rw [this]; ring

/-- `W(U,V) ≤ U V H_U²`: PROVED. -/
theorem W_le (U V : ℕ) :
    ((W U V).card : ℝ) ≤ V * U * (∑ e ∈ Icc 1 U, ((e : ℝ))⁻¹) ^ 2 := by
  have hmaps : ∀ y ∈ W U V, (y.1.1, y.2.1) ∈ Icc 1 U ×ˢ Icc 1 U := by
    intro y hy
    simp only [W, mem_filter, mem_product] at hy
    exact mem_product.mpr ⟨hy.1.1.1, hy.1.2.1⟩
  rw [card_eq_sum_card_fiberwise hmaps, sum_product]
  push_cast
  calc ∑ u ∈ Icc 1 U, ∑ s ∈ Icc 1 U,
        (((W U V).filter (fun y => (y.1.1, y.2.1) = (u, s))).card : ℝ)
      ≤ ∑ u ∈ Icc 1 U, ∑ s ∈ Icc 1 U, (V : ℝ) * (((Nat.gcd s u : ℕ) : ℝ) / s) := by
        refine sum_le_sum fun u hu => sum_le_sum fun s hs => ?_
        have hs1 := (mem_Icc.mp hs).1
        have hg : 0 < Nat.gcd s u := Nat.gcd_pos_of_pos_left _ (by omega)
        have hf := fibre_le U V u s hs1
        have hsg : 0 < s / Nat.gcd s u :=
          Nat.div_pos (Nat.gcd_le_left _ (by omega)) hg
        calc (((W U V).filter (fun y => (y.1.1, y.2.1) = (u, s))).card : ℝ)
            ≤ ((V / (s / Nat.gcd s u) : ℕ) : ℝ) := by exact_mod_cast hf
          _ ≤ (V : ℝ) / ((s / Nat.gcd s u : ℕ) : ℝ) := Nat.cast_div_le
          _ = (V : ℝ) * (((Nat.gcd s u : ℕ) : ℝ) / s) := by
              rw [Nat.cast_div (Nat.gcd_dvd_left s u) (by exact_mod_cast hg.ne')]
              have : (s : ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
              have : ((Nat.gcd s u : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
              field_simp
    _ = V * ∑ u ∈ Icc 1 U, ∑ s ∈ Icc 1 U, (((Nat.gcd s u : ℕ) : ℝ) / s) := by
        rw [mul_sum]; simp_rw [mul_sum]
    _ ≤ V * (U * (∑ e ∈ Icc 1 U, ((e : ℝ))⁻¹) ^ 2) :=
        mul_le_mul_of_nonneg_left (gcd_sum_le U) (Nat.cast_nonneg V)
    _ = _ := by ring

/-- The quadruple count: `Q4 N ≤ N² + 4 N² (1 + log N)²`: PROVED. -/
theorem Q4_le (N : ℕ) :
    ((Q4 N).card : ℝ) ≤ (N : ℝ) ^ 2 + 4 * (N : ℝ) ^ 2 * (1 + Real.log N) ^ 2 := by
  have h1 : ((Q4 N).card : ℝ) ≤ (N : ℝ) ^ 2 + 2 * (W N (2 * N)).card := by
    exact_mod_cast Q4_le_W N
  have h2 := W_le N (2 * N)
  have hH0 : 0 ≤ ∑ e ∈ Icc 1 N, ((e : ℝ))⁻¹ := sum_nonneg fun _ _ => by positivity
  have h3 := harm_le N
  have h4 : (∑ e ∈ Icc 1 N, ((e : ℝ))⁻¹) ^ 2 ≤ (1 + Real.log N) ^ 2 :=
    pow_le_pow_left₀ hH0 h3 2
  push_cast at h2
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have : 2 * (N : ℝ) * N * (∑ e ∈ Icc 1 N, ((e : ℝ))⁻¹) ^ 2 ≤
      2 * (N : ℝ) * N * (1 + Real.log N) ^ 2 :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  nlinarith

/-- Display (5.10), PROVED: `∫ |f|⁴ ≤ 5 N² (log N²)²` for `N ≥ 4`, the lab's `Display510 5 2 N`. -/
theorem display510_proved (N : ℕ) (hN : 4 ≤ N) : Display510 5 2 N := by
  unfold Display510
  rw [integral_eq_Q4]
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hL := one_le_log hN4
  have hlog2 : Real.log ((N : ℝ) ^ 2) = 2 * Real.log N := by
    rw [Real.log_pow]; push_cast; ring
  rw [hlog2]
  have hq := Q4_le N
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  have hb : (1 + Real.log N) ^ 2 ≤ 4 * Real.log N ^ 2 := by nlinarith
  have hb2 : (1 : ℝ) ≤ Real.log N ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hb hN2, mul_le_mul_of_nonneg_left hb2 hN2]

/-- The Section 5 inputs without (5.10): Lemma 1 at `P ≥ X^{2/5}` and the major arc output. -/
def Section5NoMomentInput (ε : ℝ) : Prop :=
  ∃ (A : ℝ) (C M N0 : ℕ), 0 ≤ A ∧ 0 < C ∧ ∀ N : ℕ, N0 < N →
    ∃ (X1 P : ℝ) (mi : Set ℝ) (𝓡 : Finset ℕ), MeasurableSet mi ∧
    ((N : ℝ) ^ 2) ^ (2 / 5 : ℝ) ≤ P ∧ Lemma1On A X1 ((N : ℝ) ^ 2) P mi ∧
    (∀ m ∈ Icc 1 N, (Reduction3.R1 (S X1 ((N : ℝ) ^ 2)) mi (2 * m ^ 2)).re ≤
      ((N : ℝ) ^ 2) ^ (1 - ε) → ∃ R0 ∈ 𝓡, R0 ∣ C * m ^ 2) ∧
    (∀ R0 ∈ 𝓡, ((N : ℝ) ^ 2) ^ (7 / 25 : ℝ) ≤ R0) ∧ 𝓡.card ≤ M

/-- CONDITIONAL ON Lemma 1 and the major arc output only, (5.10) now PROVED: Theorem 5. -/
theorem theorem5_of_noMomentInput (h : ∀ ε : ℝ, 0 < ε → Section5NoMomentInput ε) :
    LeanLab.ExceptionalSet.Pintz2021.Theorem5 := by
  apply theorem5_of_paperInput
  intro ε hε
  obtain ⟨A, C, M, N0, hA, hC, hin⟩ := h ε hε
  refine ⟨A, 5, 2, C, M, max N0 4, hA, by norm_num, hC, fun N hN => ?_⟩
  obtain ⟨X1, P, mi, 𝓡, hmi, hP, hL1, hMa, hPs, hM⟩ :=
    hin N (lt_of_le_of_lt (le_max_left _ _) hN)
  exact ⟨X1, P, mi, 𝓡, hmi, hP, hL1,
    display510_proved N (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hN)), hMa, hPs, hM⟩

/-- Vacuity test: the count is genuinely of order at least `N²`, the diagonal `n₁ = n₃`,
`n₂ = n₄`, so the bound `N² L²` is sharp up to the power of `L`. -/
theorem Q4_ge (N : ℕ) : N ^ 2 ≤ (Q4 N).card := by
  have : (Icc 1 N ×ˢ Icc 1 N).card ≤ (Q4 N).card := by
    refine card_le_card_of_injOn (fun p => (p, p)) ?_ ?_
    · intro p hp
      rw [mem_coe] at hp
      rw [mem_coe, Q4, mem_filter]
      exact ⟨mem_product.mpr ⟨hp, hp⟩, rfl⟩
    · intro p _ q _ h
      exact (Prod.mk.inj h).1
  simpa [card_product, sq] using this

/-- Vacuity test for `Section5NoMomentInput`: binary Goldbach, which is OPEN, does not by
itself give Lemma 1, so no shortcut; here we only check the conclusion type is the lab's
Theorem 5 and that the hypothesis `Display510` was the only clause removed. -/
theorem noMoment_of_paper {ε : ℝ} (h : Holder511.Section5PaperInput ε) :
    Section5NoMomentInput ε := by
  obtain ⟨A, K0, c, C, M, N0, hA, _, hC, hin⟩ := h
  refine ⟨A, C, M, N0, hA, hC, fun N hN => ?_⟩
  obtain ⟨X1, P, mi, 𝓡, hmi, hP, hL1, _, hMa, hPs, hM⟩ := hin N hN
  exact ⟨X1, P, mi, 𝓡, hmi, hP, hL1, hMa, hPs, hM⟩

end LeanLab.Pintz2021.Moment510U1357

#print axioms LeanLab.Pintz2021.Moment510U1357.integral_eq_Q4
#print axioms LeanLab.Pintz2021.Moment510U1357.card_diag_le
#print axioms LeanLab.Pintz2021.Moment510U1357.card_lt_le
#print axioms LeanLab.Pintz2021.Moment510U1357.card_gt_le
#print axioms LeanLab.Pintz2021.Moment510U1357.Q4_le_W
#print axioms LeanLab.Pintz2021.Moment510U1357.fibre_le
#print axioms LeanLab.Pintz2021.Moment510U1357.harm_le
#print axioms LeanLab.Pintz2021.Moment510U1357.sum_multiples_le
#print axioms LeanLab.Pintz2021.Moment510U1357.gcd_sum_le
#print axioms LeanLab.Pintz2021.Moment510U1357.W_le
#print axioms LeanLab.Pintz2021.Moment510U1357.Q4_le
#print axioms LeanLab.Pintz2021.Moment510U1357.display510_proved
#print axioms LeanLab.Pintz2021.Moment510U1357.theorem5_of_noMomentInput
#print axioms LeanLab.Pintz2021.Moment510U1357.Q4_ge
#print axioms LeanLab.Pintz2021.Moment510U1357.noMoment_of_paper
