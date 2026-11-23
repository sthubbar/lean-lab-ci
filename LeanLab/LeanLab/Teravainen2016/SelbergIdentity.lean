/-
P0076, Section 4, Proposition 4.1 v, page 17.
The Selberg normalization efs_selberg_identity of EnvelopingFourierSplit.lean, split into
multiplicative lemmas and an assembly by diagonalizing the quadratic form.
All lemmas are proved; no LEAF remains.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.EnvelopingFourierSplit

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- Helper lemmas, page 15 to 17 of P0076: support, Moebius sums and the multiplicative
structure of g and h on the divisors of P of z. -/
theorem sel_mu_sq (w : ℕ) (hw : 5 ≤ w) (z : ℝ) {f : ℕ}
    (hf : f ∈ (envelopingPrimeProduct w z).divisors) :
    (ArithmeticFunction.moebius f : ℝ) ^ 2 = 1 := by
  have hsq := (enveloping_divisor_support (J := 5) hw (Nat.dvd_of_mem_divisors hf)).1
  rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
  push_cast
  rw [← pow_mul, mul_comm, pow_mul]
  simp

theorem sel_h_ne (w : ℕ) (hw : 5 ≤ w) (z : ℝ) {f : ℕ}
    (hf : f ∈ (envelopingPrimeProduct w z).divisors) : envelopingH w f ≠ 0 := by
  have hfP := Nat.dvd_of_mem_divisors hf
  have hsq := (enveloping_divisor_support (J := 5) hw hfP).1
  unfold envelopingH
  rw [if_pos hsq, prod_ne_zero_iff]
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hwp : w < p := efs_prime_gt hpp (dvd_trans (Nat.dvd_of_mem_primeFactors hp) hfP)
  unfold envelopingOmega
  rw [if_neg (by omega)]
  split_ifs
  · apply div_ne_zero (by norm_num)
    exact Nat.cast_ne_zero.mpr (by omega)
  · apply div_ne_zero (by norm_num)
    exact Nat.cast_ne_zero.mpr (by omega)

theorem sel_h_dvd (w : ℕ) {z : ℝ} {δ : ℕ} (hδz : (δ : ℝ) ≤ z) (hh : envelopingH w δ ≠ 0) :
    δ ∣ envelopingPrimeProduct w z := by
  unfold envelopingH at hh
  split_ifs at hh with hsq
  · rw [prod_ne_zero_iff] at hh
    rw [← Nat.prod_primeFactors_of_squarefree hsq, envelopingPrimeProduct]
    apply prod_dvd_prod_of_subset
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hδ0 : δ ≠ 0 := (Nat.mem_primeFactors.mp hp).2.2
    have hpd' : p ≤ δ := Nat.le_of_dvd (Nat.pos_of_ne_zero hδ0) (Nat.dvd_of_mem_primeFactors hp)
    have hpz : (p : ℝ) ≤ z := le_trans (by exact_mod_cast hpd') hδz
    have hwp : w < p := by
      by_contra hc
      apply hh p hp
      simp [envelopingOmega, show p ≤ w by omega]
    refine mem_filter.mpr ⟨mem_range.mpr ?_, hpp, hwp, hpz⟩
    have := Nat.le_floor hpz
    omega
  · exact absurd rfl hh

theorem sel_G1 (w : ℕ) (hw : 5 ≤ w) (z : ℝ) (hz : 1 ≤ z) :
    envelopingG w 1 z =
      ∑ e ∈ (envelopingPrimeProduct w z).divisors,
        (if (e : ℝ) ≤ z then envelopingH w e else 0) := by
  rw [← sum_filter]
  unfold envelopingG
  symm
  apply sum_subset
  · intro e he
    obtain ⟨he1, he2⟩ := mem_filter.mp he
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors he1, Nat.le_floor he2⟩, ?_⟩
    simpa using he2
  · intro δ hδ hδn
    obtain ⟨-, hδz⟩ := mem_filter.mp hδ
    simp only [Nat.lcm_one_left] at hδz
    by_contra hne
    apply hδn
    refine mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨sel_h_dvd w hδz hne,
      envelopingPrimeProduct_ne_zero w z⟩, hδz⟩

theorem sel_sum_mu (k : ℕ) :
    ∑ j ∈ k.divisors, (ArithmeticFunction.moebius j : ℝ) = if k = 1 then 1 else 0 := by
  have h := congrArg (fun F : ArithmeticFunction ℤ => F k) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  rw [← Int.cast_sum, h]
  split_ifs <;> simp

theorem sel_moebius (w : ℕ) (hw : 5 ≤ w) (z : ℝ) {f e : ℕ}
    (hf : f ∈ (envelopingPrimeProduct w z).divisors)
    (he : e ∈ (envelopingPrimeProduct w z).divisors) :
    ∑ d ∈ (envelopingPrimeProduct w z).divisors,
      (if f ∣ d ∧ d ∣ e then (ArithmeticFunction.moebius d : ℝ) else 0) =
      if f = e then (ArithmeticFunction.moebius f : ℝ) else 0 := by
  have heP := Nat.dvd_of_mem_divisors he
  have hP := envelopingPrimeProduct_ne_zero w z
  have he0 : e ≠ 0 := fun h => hP (Nat.eq_zero_of_zero_dvd (h ▸ heP))
  have hsq := (enveloping_divisor_support (J := 5) hw heP).1
  by_cases hfe : f ∣ e
  · obtain ⟨k, rfl⟩ := hfe
    have hf0 : f ≠ 0 := left_ne_zero_of_mul he0
    have hk0 : k ≠ 0 := right_ne_zero_of_mul he0
    have hcop : Nat.Coprime f k := Nat.coprime_of_squarefree_mul hsq
    rw [← sum_filter]
    have hset : (envelopingPrimeProduct w z).divisors.filter (fun d => f ∣ d ∧ d ∣ f * k) =
        k.divisors.image (fun j => f * j) := by
      ext d
      simp only [mem_filter, Nat.mem_divisors, mem_image]
      constructor
      · rintro ⟨-, ⟨j, rfl⟩, hd⟩
        exact ⟨j, ⟨(Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hf0)).mp hd, hk0⟩, rfl⟩
      · rintro ⟨j, ⟨hj, -⟩, rfl⟩
        refine ⟨⟨dvd_trans (mul_dvd_mul_left f hj) heP, hP⟩, dvd_mul_right _ _,
          mul_dvd_mul_left f hj⟩
    rw [hset, sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hf0) h)]
    have hmul : ∀ j ∈ k.divisors, (ArithmeticFunction.moebius (f * j) : ℝ) =
        (ArithmeticFunction.moebius f : ℝ) * ArithmeticFunction.moebius j := by
      intro j hj
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        (Nat.Coprime.coprime_dvd_right (Nat.dvd_of_mem_divisors hj) hcop)]
      push_cast; ring
    rw [sum_congr rfl hmul, ← mul_sum, sel_sum_mu]
    by_cases hk1 : k = 1
    · subst hk1; simp
    · have : f ≠ f * k := by
        intro h
        apply hk1
        have := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hf0) (h.symm.trans (mul_one f).symm)
        exact this
      simp [hk1, this]
  · have hne : f ≠ e := fun h => hfe (h ▸ dvd_rfl)
    rw [if_neg hne]
    apply sum_eq_zero
    intro d _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hfe (dvd_trans h1 h2)

theorem sel_divisors_image {n : ℕ} (hn : Squarefree n) :
    n.divisors = n.primeFactors.powerset.image (fun t => ∏ p ∈ t, p) := by
  have hn0 : n ≠ 0 := hn.ne_zero
  ext d
  simp only [Nat.mem_divisors, mem_image, mem_powerset]
  constructor
  · rintro ⟨hd, -⟩
    refine ⟨d.primeFactors, Nat.primeFactors_mono hd hn0, ?_⟩
    exact Nat.prod_primeFactors_of_squarefree (hn.squarefree_of_dvd hd)
  · rintro ⟨t, ht, rfl⟩
    refine ⟨?_, hn0⟩
    calc ∏ p ∈ t, p ∣ ∏ p ∈ n.primeFactors, p := prod_dvd_prod_of_subset _ _ _ ht
      _ = n := Nat.prod_primeFactors_of_squarefree hn

theorem sel_sum_divisors {n : ℕ} (hn : Squarefree n) (F : ℕ → ℝ) :
    ∑ f ∈ n.divisors, F f = ∑ t ∈ n.primeFactors.powerset, F (∏ p ∈ t, p) := by
  rw [sel_divisors_image hn, sum_image]
  intro a ha b hb hab
  have hpa : ∀ p ∈ a, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (mem_powerset.mp ha hp)
  have hpb : ∀ p ∈ b, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (mem_powerset.mp hb hp)
  rw [← Nat.primeFactors_prod hpa, ← Nat.primeFactors_prod hpb]
  exact congrArg Nat.primeFactors hab

theorem sel_h_prod (w : ℕ) {n : ℕ} (hn : Squarefree n) {t : Finset ℕ}
    (ht : t ⊆ n.primeFactors) :
    envelopingH w (∏ p ∈ t, p) =
      ∏ p ∈ t, (envelopingOmega w p : ℝ) / (p - envelopingOmega w p : ℕ) := by
  have hpt : ∀ p ∈ t, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (ht hp)
  have hdvd : ∏ p ∈ t, p ∣ n := by
    calc ∏ p ∈ t, p ∣ ∏ p ∈ n.primeFactors, p := prod_dvd_prod_of_subset _ _ _ ht
      _ = n := Nat.prod_primeFactors_of_squarefree hn
  unfold envelopingH
  rw [if_pos (hn.squarefree_of_dvd hdvd), Nat.primeFactors_prod hpt]

/-- 1 over g of n is the sum of 1 over h f over f dividing n, for n dividing P. -/
theorem sel_inv_g (w : ℕ) (hw : 5 ≤ w) (z : ℝ) {n : ℕ}
    (hn : n ∣ envelopingPrimeProduct w z) :
    ∑ f ∈ n.divisors, (envelopingH w f)⁻¹ = (envelopingDensity w n)⁻¹ := by
  have hsq := (enveloping_divisor_support (J := 5) hw hn).1
  rw [sel_sum_divisors hsq]
  rw [sum_congr rfl (fun t ht => by rw [sel_h_prod w hsq (mem_powerset.mp ht), ← prod_inv_distrib])]
  rw [← prod_one_add, envelopingDensity, ← prod_inv_distrib]
  apply prod_congr rfl
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hwp : w < p := efs_prime_gt hpp (dvd_trans (Nat.dvd_of_mem_primeFactors hp) hn)
  unfold envelopingOmega
  rw [if_neg (by omega)]
  have hp6 : (6 : ℝ) ≤ p := by exact_mod_cast (show 6 ≤ p by omega)
  split_ifs
  · rw [Nat.cast_sub (by omega)]
    field_simp
    push_cast
    ring_nf
  · rw [Nat.cast_sub (by omega)]
    field_simp
    push_cast
    ring_nf


theorem sel_g_ne (w : ℕ) (z : ℝ) {n : ℕ} (hn : n ∣ envelopingPrimeProduct w z) :
    envelopingDensity w n ≠ 0 := by
  unfold envelopingDensity
  rw [prod_ne_zero_iff]
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hwp : w < p := efs_prime_gt hpp (dvd_trans (Nat.dvd_of_mem_primeFactors hp) hn)
  unfold envelopingOmega
  rw [if_neg (by omega)]
  have : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpp.ne_zero
  split_ifs <;> simp [this]

theorem sel_g_lcm (w : ℕ) (hw : 5 ≤ w) (z : ℝ) {d1 d2 : ℕ}
    (hd1 : d1 ∈ (envelopingPrimeProduct w z).divisors)
    (hd2 : d2 ∈ (envelopingPrimeProduct w z).divisors) :
    envelopingDensity w (Nat.lcm d1 d2) =
      envelopingDensity w d1 * envelopingDensity w d2 *
        ∑ f ∈ (envelopingPrimeProduct w z).divisors,
          (if f ∣ d1 then (1 : ℝ) else 0) * (if f ∣ d2 then (1 : ℝ) else 0) / envelopingH w f := by
  have hP := envelopingPrimeProduct_ne_zero w z
  have hd1P := Nat.dvd_of_mem_divisors hd1
  have hd2P := Nat.dvd_of_mem_divisors hd2
  have h1 : d1 ≠ 0 := fun h => hP (Nat.eq_zero_of_zero_dvd (h ▸ hd1P))
  have h2 : d2 ≠ 0 := fun h => hP (Nat.eq_zero_of_zero_dvd (h ▸ hd2P))
  have hgP : Nat.gcd d1 d2 ∣ envelopingPrimeProduct w z := dvd_trans (Nat.gcd_dvd_left _ _) hd1P
  have hsum : ∑ f ∈ (envelopingPrimeProduct w z).divisors,
      (if f ∣ d1 then (1 : ℝ) else 0) * (if f ∣ d2 then (1 : ℝ) else 0) / envelopingH w f =
      (envelopingDensity w (Nat.gcd d1 d2))⁻¹ := by
    rw [← sel_inv_g w hw z hgP]
    have hc : ∀ f ∈ (envelopingPrimeProduct w z).divisors,
        (if f ∣ d1 then (1 : ℝ) else 0) * (if f ∣ d2 then (1 : ℝ) else 0) / envelopingH w f =
        if f ∣ Nat.gcd d1 d2 then (envelopingH w f)⁻¹ else 0 := by
      intro f _
      simp only [Nat.dvd_gcd_iff]
      by_cases a : f ∣ d1 <;> by_cases b : f ∣ d2 <;> simp [a, b]
    rw [sum_congr rfl hc, ← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext f
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨-, h⟩
      exact ⟨h, Nat.gcd_ne_zero_left h1⟩
    · rintro ⟨h, -⟩
      exact ⟨⟨dvd_trans h hgP, hP⟩, h⟩
  have hpf : (Nat.lcm d1 d2).primeFactors = (d1 * d2).primeFactors := by
    rw [Nat.primeFactors_mul h1 h2]
    ext p
    simp only [Finset.mem_union, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hpd, -⟩
      rcases (Nat.Prime.dvd_mul hp).mp (dvd_trans hpd (Nat.lcm_dvd_mul d1 d2)) with h | h
      · exact Or.inl ⟨hp, h, h1⟩
      · exact Or.inr ⟨hp, h, h2⟩
    · rintro (⟨hp, h, -⟩ | ⟨hp, h, -⟩)
      · exact ⟨hp, dvd_trans h (Nat.dvd_lcm_left _ _), Nat.lcm_ne_zero h1 h2⟩
      · exact ⟨hp, dvd_trans h (Nat.dvd_lcm_right _ _), Nat.lcm_ne_zero h1 h2⟩
  have hmain : envelopingDensity w (Nat.gcd d1 d2) * envelopingDensity w (Nat.lcm d1 d2) =
      envelopingDensity w d1 * envelopingDensity w d2 := by
    unfold envelopingDensity
    rw [hpf]
    exact Nat.prod_primeFactors_gcd_mul_prod_primeFactors_mul d1 d2 _
  rw [hsum, ← hmain]
  have := sel_g_ne w z hgP
  field_simp

theorem sel_pf_lcm {a b : ℕ} (h1 : a ≠ 0) (h2 : b ≠ 0) :
    (Nat.lcm a b).primeFactors = a.primeFactors ∪ b.primeFactors := by
  ext p
  simp only [Finset.mem_union, Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hpd, -⟩
    rcases (Nat.Prime.dvd_mul hp).mp (dvd_trans hpd (Nat.lcm_dvd_mul a b)) with h | h
    · exact Or.inl ⟨hp, h, h1⟩
    · exact Or.inr ⟨hp, h, h2⟩
  · rintro (⟨hp, h, -⟩ | ⟨hp, h, -⟩)
    · exact ⟨hp, dvd_trans h (Nat.dvd_lcm_left _ _), Nat.lcm_ne_zero h1 h2⟩
    · exact ⟨hp, dvd_trans h (Nat.dvd_lcm_right _ _), Nat.lcm_ne_zero h1 h2⟩

theorem sel_local (w : ℕ) (hw : 5 ≤ w) (z : ℝ) {p : ℕ} (hp : p.Prime)
    (hpP : p ∣ envelopingPrimeProduct w z) :
    (envelopingOmega w p : ℝ) / p *
      ((envelopingOmega w p : ℝ) / (p - envelopingOmega w p : ℕ) + 1) =
      (envelopingOmega w p : ℝ) / (p - envelopingOmega w p : ℕ) := by
  have hwp : w < p := efs_prime_gt hp hpP
  unfold envelopingOmega
  rw [if_neg (by omega)]
  have hp6 : (6 : ℝ) ≤ p := by exact_mod_cast (show 6 ≤ p by omega)
  split_ifs
  · rw [Nat.cast_sub (by omega)]
    have : (p : ℝ) - 1 ≠ 0 := by linarith
    push_cast
    field_simp
    ring
  · rw [Nat.cast_sub (by omega)]
    have : (p : ℝ) - 2 ≠ 0 := by linarith
    push_cast
    field_simp
    ring

/-- Page 15, the fibre of delta to lcm d delta over e carries mass h e over g d. -/
theorem sel_K (w : ℕ) (hw : 5 ≤ w) (z : ℝ) {d e : ℕ} (hde : d ∣ e)
    (he : e ∣ envelopingPrimeProduct w z) :
    envelopingDensity w d *
      ∑ δ ∈ (envelopingPrimeProduct w z).divisors,
        (if Nat.lcm d δ = e then envelopingH w δ else 0) = envelopingH w e := by
  have hP := envelopingPrimeProduct_ne_zero w z
  have he0 : e ≠ 0 := fun h => hP (Nat.eq_zero_of_zero_dvd (h ▸ he))
  have hd0 : d ≠ 0 := fun h => he0 (Nat.eq_zero_of_zero_dvd (h ▸ hde))
  have hsq := (enveloping_divisor_support (J := 5) hw he).1
  set E := e.primeFactors with hE
  set Dp := d.primeFactors with hDp
  have hDE : Dp ⊆ E := Nat.primeFactors_mono hde he0
  set hp : ℕ → ℝ := fun p =>
    (envelopingOmega w p : ℝ) / (p - envelopingOmega w p : ℕ) with hhp
  -- step a
  have ha : ∑ δ ∈ (envelopingPrimeProduct w z).divisors,
      (if Nat.lcm d δ = e then envelopingH w δ else 0) =
      ∑ δ ∈ e.divisors, (if Nat.lcm d δ = e then envelopingH w δ else 0) := by
    symm
    apply sum_subset
    · intro δ hδ
      exact Nat.mem_divisors.mpr ⟨dvd_trans (Nat.dvd_of_mem_divisors hδ) he, hP⟩
    · intro δ _ hδ
      rw [if_neg]
      intro hl
      apply hδ
      exact Nat.mem_divisors.mpr ⟨hl ▸ Nat.dvd_lcm_right d δ, he0⟩
  -- steps b and c
  have hc : ∀ t ∈ E.powerset,
      (if Nat.lcm d (∏ p ∈ t, p) = e then envelopingH w (∏ p ∈ t, p) else 0) =
      (∏ p ∈ t, hp p) * ∏ p ∈ E \ t, (if p ∈ Dp then (1 : ℝ) else 0) := by
    intro t ht
    have htE : t ⊆ E := mem_powerset.mp ht
    have hpt : ∀ p ∈ t, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (htE hp)
    have htdvd : ∏ p ∈ t, p ∣ e := by
      calc ∏ p ∈ t, p ∣ ∏ p ∈ e.primeFactors, p := prod_dvd_prod_of_subset _ _ _ htE
        _ = e := Nat.prod_primeFactors_of_squarefree hsq
    have ht0 : ∏ p ∈ t, p ≠ 0 := fun h => he0 (Nat.eq_zero_of_zero_dvd (h ▸ htdvd))
    have hiff : Nat.lcm d (∏ p ∈ t, p) = e ↔ E \ t ⊆ Dp := by
      have hpf := sel_pf_lcm hd0 ht0
      rw [Nat.primeFactors_prod hpt] at hpf
      constructor
      · intro hl q hq
        rw [mem_sdiff] at hq
        have : q ∈ (Nat.lcm d (∏ p ∈ t, p)).primeFactors := by rw [hl]; exact hq.1
        rw [hpf, mem_union] at this
        rcases this with h | h
        · exact h
        · exact absurd h hq.2
      · intro hsub
        have hl : Nat.lcm d (∏ p ∈ t, p) ∣ e := Nat.lcm_dvd hde htdvd
        have hlsq := hsq.squarefree_of_dvd hl
        rw [← Nat.prod_primeFactors_of_squarefree hlsq, ← Nat.prod_primeFactors_of_squarefree hsq,
          hpf]
        congr 1
        ext q
        rw [mem_union]
        constructor
        · rintro (h | h)
          · exact hDE h
          · exact htE h
        · intro hq
          by_cases hqt : q ∈ t
          · exact Or.inr hqt
          · exact Or.inl (hsub (mem_sdiff.mpr ⟨hq, hqt⟩))
    have hbool : ∏ p ∈ E \ t, (if p ∈ Dp then (1 : ℝ) else 0) =
        if E \ t ⊆ Dp then 1 else 0 := by
      split_ifs with hs
      · exact prod_eq_one (fun p hp => if_pos (hs hp))
      · rw [not_subset] at hs
        obtain ⟨q, hq, hqD⟩ := hs
        exact prod_eq_zero hq (if_neg hqD)
    rw [hbool, sel_h_prod w hsq htE]
    by_cases hs : E \ t ⊆ Dp
    · rw [if_pos (hiff.mpr hs), if_pos hs, mul_one]
    · rw [if_neg (fun h => hs (hiff.mp h)), if_neg hs, mul_zero]
  rw [ha, sel_sum_divisors hsq, sum_congr rfl hc, ← prod_add]
  -- step e
  have hsplit : ∀ F : ℕ → ℝ, ∏ p ∈ E, F p = (∏ p ∈ Dp, F p) * ∏ p ∈ E.filter (· ∉ Dp), F p := by
    intro F
    rw [← prod_filter_mul_prod_filter_not E (· ∈ Dp)]
    congr 2
    ext q
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hDE h, h⟩⟩
  have hhe : envelopingH w e = ∏ p ∈ E, hp p := by
    unfold envelopingH; rw [if_pos hsq]
  rw [hhe, hsplit, hsplit hp]
  have h1 : ∏ p ∈ E.filter (· ∉ Dp), (hp p + if p ∈ Dp then (1 : ℝ) else 0) =
      ∏ p ∈ E.filter (· ∉ Dp), hp p :=
    prod_congr rfl (fun p hpm => by rw [if_neg (mem_filter.mp hpm).2, add_zero])
  have h2 : envelopingDensity w d * ∏ p ∈ Dp, (hp p + if p ∈ Dp then (1 : ℝ) else 0) =
      ∏ p ∈ Dp, hp p := by
    unfold envelopingDensity
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro p hpD
    rw [if_pos hpD]
    exact sel_local w hw z (Nat.prime_of_mem_primeFactors hpD)
      (dvd_trans (dvd_trans (Nat.dvd_of_mem_primeFactors hpD) hde) he)
  rw [h1, ← mul_assoc, h2]


/-- Page 15 of P0076 and Ramare and Ruzsa reference 18 section 4.1, the lcm
reparametrization: for d dividing P of z, g of d times G_d of z is the sum of h of e over
the divisors e of P of z that are multiples of d and at most z. -/
theorem sel_gG (w : ℕ) (hw : 5 ≤ w) (z : ℝ) (hz : 1 ≤ z) {d : ℕ}
    (hd : d ∈ (envelopingPrimeProduct w z).divisors) :
    envelopingDensity w d * envelopingG w d z =
      ∑ e ∈ (envelopingPrimeProduct w z).divisors,
        (if d ∣ e ∧ (e : ℝ) ≤ z then envelopingH w e else 0) := by
  have hP := envelopingPrimeProduct_ne_zero w z
  have hdP := Nat.dvd_of_mem_divisors hd
  set D := (envelopingPrimeProduct w z).divisors with hD
  have hGd : envelopingG w d z =
      ∑ δ ∈ D, (if (Nat.lcm d δ : ℝ) ≤ z then envelopingH w δ else 0) := by
    rw [← sum_filter]
    unfold envelopingG
    symm
    apply sum_subset
    · intro δ hδ
      obtain ⟨hδ1, hδ2⟩ := mem_filter.mp hδ
      have hδ0 : δ ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hδ1)
      have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
      have hδle : δ ≤ Nat.lcm d δ :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.lcm_ne_zero hd0 hδ0)) (Nat.dvd_lcm_right d δ)
      have hle : (δ : ℝ) ≤ z := le_trans (by exact_mod_cast hδle) hδ2
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hδ1, Nat.le_floor hle⟩, hδ2⟩
    · intro δ hδ hδn
      obtain ⟨hδI, hδz⟩ := mem_filter.mp hδ
      have hδ0 : δ ≠ 0 := by have := (mem_Icc.mp hδI).1; omega
      have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
      have hδle : δ ≤ Nat.lcm d δ :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.lcm_ne_zero hd0 hδ0)) (Nat.dvd_lcm_right d δ)
      have hle : (δ : ℝ) ≤ z := le_trans (by exact_mod_cast hδle) hδz
      by_contra hne
      exact hδn (mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨sel_h_dvd w hle hne, hP⟩, hδz⟩)
  have hR : ∀ e ∈ D, (if d ∣ e ∧ (e : ℝ) ≤ z then envelopingH w e else 0) =
      ∑ δ ∈ D, envelopingDensity w d *
        (if d ∣ e ∧ (e : ℝ) ≤ z then (if Nat.lcm d δ = e then envelopingH w δ else 0) else 0) := by
    intro e he
    split_ifs with h
    · rw [← mul_sum, sel_K w hw z h.1 (Nat.dvd_of_mem_divisors he)]
    · simp
  rw [sum_congr rfl hR, sum_comm, hGd, mul_sum]
  refine sum_congr rfl (fun δ hδ => ?_)
  rw [← mul_sum]
  congr 1
  have hlP : Nat.lcm d δ ∈ D :=
    Nat.mem_divisors.mpr ⟨Nat.lcm_dvd hdP (Nat.dvd_of_mem_divisors hδ), hP⟩
  have hx : ∀ e ∈ D, (if d ∣ e ∧ (e : ℝ) ≤ z then
      (if Nat.lcm d δ = e then envelopingH w δ else 0) else 0) =
      if Nat.lcm d δ = e then (if (Nat.lcm d δ : ℝ) ≤ z then envelopingH w δ else 0) else 0 := by
    intro e _
    by_cases hl : Nat.lcm d δ = e
    · subst hl
      simp [Nat.dvd_lcm_left]
    · simp [hl]
  rw [sum_congr rfl hx, sum_ite_eq D (Nat.lcm d δ), if_pos hlP]

/-- Page 17, the linear forms y_f of the diagonalized quadratic form. -/
theorem sel_y (w : ℕ) (hw : 5 ≤ w) (z : ℝ) (hz : 1 ≤ z) {f : ℕ}
    (hf : f ∈ (envelopingPrimeProduct w z).divisors) :
    ∑ d ∈ (envelopingPrimeProduct w z).divisors,
      envelopingRho w d z * envelopingDensity w d * (if f ∣ d then (1 : ℝ) else 0) =
      if (f : ℝ) ≤ z then
        (ArithmeticFunction.moebius f : ℝ) * envelopingH w f / envelopingG w 1 z else 0 := by
  set D := (envelopingPrimeProduct w z).divisors
  set G := envelopingG w 1 z
  have step1 : ∀ d ∈ D,
      envelopingRho w d z * envelopingDensity w d * (if f ∣ d then (1 : ℝ) else 0) =
      ∑ e ∈ D, (if (e : ℝ) ≤ z then envelopingH w e else 0) / G *
        (if f ∣ d ∧ d ∣ e then (ArithmeticFunction.moebius d : ℝ) else 0) := by
    intro d hd
    have h1 : envelopingRho w d z * envelopingDensity w d =
        (ArithmeticFunction.moebius d : ℝ) / G *
          (envelopingDensity w d * envelopingG w d z) := by
      unfold envelopingRho; ring
    rw [h1, sel_gG w hw z hz hd, mul_sum, sum_mul]
    refine sum_congr rfl (fun e _ => ?_)
    by_cases hfd : f ∣ d <;> by_cases hde : d ∣ e <;> by_cases hez : (e : ℝ) ≤ z <;>
      simp [hfd, hde, hez]; ring
  rw [sum_congr rfl step1, sum_comm]
  simp_rw [← mul_sum]
  rw [sum_congr rfl (fun e he => by rw [sel_moebius w hw z hf he])]
  simp only [mul_ite, mul_zero]
  rw [sum_ite_eq D f]
  simp only [hf, ite_true]
  split_ifs <;> ring

/-- Proposition 4.1 v, page 17 of P0076, the Selberg normalization, with exactly the
statement of efs_selberg_identity. Proved, with no LEAF left. -/
theorem efs_selberg_identity_proved {w : ℕ} (hw : 5 ≤ w) {z : ℝ} (hz : 1 ≤ z) :
    envelopingG w 1 z *
      ∑ d1 ∈ (envelopingPrimeProduct w z).divisors, ∑ d2 ∈ (envelopingPrimeProduct w z).divisors,
        envelopingRho w d1 z * envelopingRho w d2 z * envelopingDensity w (Nat.lcm d1 d2) = 1 := by
  set D := (envelopingPrimeProduct w z).divisors with hD
  set G := envelopingG w 1 z with hGdef
  have hG : G ≠ 0 := (lt_of_lt_of_le one_pos (envelopingG_one_le w hz)).ne'
  set a : ℕ → ℕ → ℝ := fun d f =>
    envelopingRho w d z * envelopingDensity w d * (if f ∣ d then (1 : ℝ) else 0) with ha
  have hexp : ∀ d1 ∈ D, ∀ d2 ∈ D,
      envelopingRho w d1 z * envelopingRho w d2 z * envelopingDensity w (Nat.lcm d1 d2) =
      ∑ f ∈ D, a d1 f * a d2 f / envelopingH w f := by
    intro d1 hd1 d2 hd2
    rw [sel_g_lcm w hw z hd1 hd2, mul_sum, mul_sum]
    refine sum_congr rfl (fun f _ => ?_)
    simp only [ha]
    ring
  have hQ : ∑ d1 ∈ D, ∑ d2 ∈ D,
      envelopingRho w d1 z * envelopingRho w d2 z * envelopingDensity w (Nat.lcm d1 d2) =
      ∑ f ∈ D, (∑ d ∈ D, a d f) * (∑ d ∈ D, a d f) / envelopingH w f := by
    rw [sum_congr rfl (fun d1 hd1 => sum_congr rfl (fun d2 hd2 => hexp d1 hd1 d2 hd2))]
    conv_rhs => simp only [sum_mul_sum, sum_div]
    rw [sum_congr rfl (fun d1 _ => sum_comm)]
    rw [sum_comm]
  have hy : ∀ f ∈ D, (∑ d ∈ D, a d f) * (∑ d ∈ D, a d f) / envelopingH w f =
      (if (f : ℝ) ≤ z then envelopingH w f else 0) / G ^ 2 := by
    intro f hf
    have hyf : ∑ d ∈ D, a d f = _ := sel_y w hw z hz hf
    rw [← hGdef] at hyf
    rw [hyf]
    have hh := sel_h_ne w hw z hf
    have hmu := sel_mu_sq w hw z hf
    split_ifs
    · field_simp
      exact hmu
    · simp
  rw [hQ, sum_congr rfl hy, ← sum_div, ← sel_G1 w hw z hz]
  field_simp
  ring

end LeanLab.Teravainen2016
