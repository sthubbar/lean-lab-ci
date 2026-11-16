/-
P0069 Baker Harman Pintz 1997, pages 6 and 7, displays 2.4 and 2.5.
The S2 replacement after display 2.5. Theorem 2 puts no coprimality condition on b,
so for a squarefree modulus q the frequencies m are sorted by g = gcd(m, q); the
condition g ∣ m is written by Moebius inclusion and exclusion through principal
characters, and every piece is a twisted sum with a character of modulus dividing q,
which hypothesis iv controls. The main terms cancel for g > 1.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib
import LeanLab.BHP1997.Route512Major

namespace LeanLab.BHP1997.Route512Major
open Classical Complex

private lemma sum_moebius512j (n : ℕ) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply,
    ArithmeticFunction.intCoe_apply] at h
  exact h

/-- P0069 page 7, the S2 replacement after display 2.5: for squarefree `g` the condition
`g ∣ k` is the Moebius sum over `d ∣ g` of the coprimality indicators of `k` and `d`. -/
theorem moebius_coprime_sum512j (g k : ℕ) (hg : Squarefree g) :
    ∑ d ∈ g.divisors, (if Nat.Coprime k d then (ArithmeticFunction.moebius d : ℂ) else 0) =
      if g ∣ k then 1 else 0 := by
  have hg0 : g ≠ 0 := hg.ne_zero
  obtain ⟨g₁, h1, h2, h3, h4⟩ : ∃ g₁ : ℕ, g₁ ∣ g ∧ g₁ ∣ k ∧ (g ∣ k → g₁ = g) ∧
      (∀ e : ℕ, e ∣ g → e ∣ k → e ∣ g₁) :=
    ⟨Nat.gcd g k, Nat.gcd_dvd_left g k, Nat.gcd_dvd_right g k, fun h => Nat.gcd_eq_left h,
      fun e he hk => Nat.dvd_gcd he hk⟩
  obtain ⟨g₂, hg₂⟩ := h1
  have hsq : Squarefree (g₁ * g₂) := by rw [← hg₂]; exact hg
  have hcop : Nat.Coprime g₁ g₂ := Nat.coprime_of_squarefree_mul hsq
  have hg₂g : g₂ ∣ g := Dvd.intro_left g₁ hg₂.symm
  have hk : Nat.Coprime g₂ k := by
    have ha : Nat.gcd g₂ k ∣ g₁ :=
      h4 _ ((Nat.gcd_dvd_left g₂ k).trans hg₂g) (Nat.gcd_dvd_right g₂ k)
    have hb : Nat.Coprime (Nat.gcd g₂ k) g₁ :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left g₂ k) hcop.symm
    exact hb.eq_one_of_dvd ha
  have hfilter : g.divisors.filter (fun d => Nat.Coprime k d) = g₂.divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, _⟩, hkd⟩
      refine ⟨?_, ?_⟩
      · have hdg : Nat.Coprime d g₁ := Nat.Coprime.coprime_dvd_right h2 hkd.symm
        rw [hg₂] at hd
        exact hdg.dvd_of_dvd_mul_left hd
      · rintro rfl
        rw [mul_zero] at hg₂
        exact hg0 hg₂
    · rintro ⟨hd, _⟩
      exact ⟨⟨hd.trans hg₂g, hg0⟩, (Nat.Coprime.coprime_dvd_left hd hk).symm⟩
  rw [← Finset.sum_filter, hfilter, sum_moebius512j]
  have hiff : g₂ = 1 ↔ g ∣ k := by
    constructor
    · intro h
      rw [h, mul_one] at hg₂
      rw [hg₂]
      exact h2
    · intro h
      have h5 := h3 h
      rw [h5] at hg₂
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hg0) (by rw [mul_one]; exact hg₂.symm)
  simp only [hiff]

private lemma changeLevel_apply512j {n : ℕ} (χ : DirichletCharacter ℂ n) (d k : ℕ) :
    (DirichletCharacter.changeLevel (Dvd.intro d rfl : n ∣ n * d) χ) (k : ZMod (n * d)) =
      if Nat.Coprime k d then χ (k : ZMod n) else 0 := by
  by_cases hu : IsUnit (k : ZMod (n * d))
  · have hc : Nat.Coprime k (n * d) := (ZMod.isUnit_iff_coprime k (n * d)).mp hu
    rw [ite_eq_left (Nat.Coprime.coprime_mul_left_right hc)]
    have h := DirichletCharacter.changeLevel_eq_cast_of_dvd χ (Dvd.intro d rfl : n ∣ n * d) hu.unit
    rw [hu.unit_spec] at h
    rw [h, ZMod.cast_natCast (Dvd.intro d rfl)]
  · rw [MulChar.map_nonunit _ hu]
    split_ifs with hkd
    · symm
      apply MulChar.map_nonunit
      rw [ZMod.isUnit_iff_coprime]
      intro hkn
      exact hu ((ZMod.isUnit_iff_coprime k (n * d)).mpr (Nat.Coprime.mul_right hkn hkd))
    · rfl

private lemma shift_gcd512j (g q' : ℕ) (hg : g ≠ 0) [NeZero q'] (j : ℕ) (r : ℤ) (η : ℝ) :
    @fourier 1 ((g * j : ℕ) : ℤ)
        (((r : ℝ) / ((g * q' : ℕ) : ℝ) + η : ℝ) : AddCircle (1 : ℝ)) =
      ZMod.stdAddChar (N := q') (((j : ℤ) * r : ℤ) : ZMod q') *
        @fourier 1 ((g * j : ℕ) : ℤ) (η : AddCircle (1 : ℝ)) := by
  rw [fourier_coe_apply, fourier_coe_apply, ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  have hg' : (g : ℂ) ≠ 0 := by exact_mod_cast hg
  have hq' : (q' : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q'
  push_cast
  field_simp

/-- P0069 page 7, the S2 replacement after display 2.5, one frequency: for squarefree `g`
coprime to `q'` and `r` a unit modulo `q'`, the indicator of `gcd(k, g q') = g` times
`e(k(r/(g q') + η))` is a combination, over the characters modulo `q'` and the divisors
`d` of `g`, of the characters of modulus `q' d` at `k`, times `e(kη)`. -/
theorem gcd_class_expansion512j (g q' : ℕ) [NeZero q'] (hg : Squarefree g)
    (hcop : Nat.Coprime g q') (r : ℤ) (hr : IsUnit (r : ZMod q')) (k : ℕ) (η : ℝ) :
    (if Nat.gcd k (g * q') = g then
        @fourier 1 (k : ℤ) (((r : ℝ) / ((g * q' : ℕ) : ℝ) + η : ℝ) : AddCircle (1 : ℝ))
      else 0) =
      (q'.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q',
        gaussSum χ⁻¹ ZMod.stdAddChar * χ (r : ZMod q') * χ⁻¹ (g : ZMod q') *
          ∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : ℂ) *
            ((DirichletCharacter.changeLevel (Dvd.intro d rfl : q' ∣ q' * d) χ)
                (k : ZMod (q' * d)) *
              @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) := by
  have hφ : (q'.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q'))).ne'
  have hg0 : 0 < g := Nat.pos_of_ne_zero hg.ne_zero
  have inner : ∀ χ : DirichletCharacter ℂ q',
      (∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : ℂ) *
        ((DirichletCharacter.changeLevel (Dvd.intro d rfl : q' ∣ q' * d) χ)
            (k : ZMod (q' * d)) *
          @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ)))) =
        (if g ∣ k then 1 else 0) *
          (χ (k : ZMod q') * @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) := by
    intro χ
    rw [← moebius_coprime_sum512j g k hg, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    rw [changeLevel_apply512j]
    split_ifs <;> ring
  simp only [inner]
  by_cases hgk : g ∣ k
  · by_cases hkq : Nat.Coprime k q'
    · have hgcd : Nat.gcd k (g * q') = g := by
        rw [Nat.Coprime.gcd_mul k hcop, Nat.gcd_eq_right hgk, hkq.gcd_eq_one, mul_one]
      rw [ite_eq_left hgcd, ite_eq_left hgk]
      obtain ⟨j, rfl⟩ := hgk
      rw [shift_gcd512j g q' hg.ne_zero j r η]
      have hj : IsUnit (j : ZMod q') :=
        (ZMod.isUnit_iff_coprime j q').mpr (Nat.Coprime.coprime_mul_left hkq)
      have hgu : IsUnit (g : ZMod q') := (ZMod.isUnit_iff_coprime g q').mpr hcop
      have hinv := gauss_inversion512j ZMod.stdAddChar ((j : ZMod q') * (r : ZMod q'))
        (hj.mul hr)
      have hχ : ∀ χ : DirichletCharacter ℂ q', χ ((j : ZMod q') * (r : ZMod q')) =
          χ (r : ZMod q') * χ⁻¹ (g : ZMod q') * χ ((g * j : ℕ) : ZMod q') := by
        intro χ
        have hne : χ (g : ZMod q') ≠ 0 := (hgu.map χ).ne_zero
        rw [MulChar.inv_apply_eq_inv', Nat.cast_mul, map_mul, map_mul]
        field_simp
      have hcast : (((j : ℤ) * r : ℤ) : ZMod q') = (j : ZMod q') * (r : ZMod q') := by
        push_cast
        rfl
      rw [hcast]
      calc
        _ = (q'.totient : ℂ)⁻¹ * ((q'.totient : ℂ) *
              ZMod.stdAddChar ((j : ZMod q') * (r : ZMod q'))) *
            @fourier 1 ((g * j : ℕ) : ℤ) (η : AddCircle (1 : ℝ)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hφ, one_mul]
        _ = _ := by
          rw [← hinv, mul_assoc, Finset.sum_mul]
          congr 1
          apply Finset.sum_congr rfl
          intro χ _
          rw [hχ χ]
          ring
    · have hgcd : Nat.gcd k (g * q') ≠ g := by
        rw [Nat.Coprime.gcd_mul k hcop, Nat.gcd_eq_right hgk]
        intro h
        exact hkq (Nat.eq_of_mul_eq_mul_left hg0 (h.trans (mul_one g).symm))
      have hz : ∀ χ : DirichletCharacter ℂ q', χ (k : ZMod q') = 0 := fun χ =>
        χ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime])
      rw [ite_eq_right hgcd]
      simp [hz]
  · have hgcd : Nat.gcd k (g * q') ≠ g := fun h =>
      hgk (h ▸ (Nat.gcd_dvd_left k (g * q')))
    rw [ite_eq_right hgcd, ite_eq_right hgk]
    simp

/-- P0069 page 7, the S2 replacement after display 2.5, one gcd class: for `q = g q'` with
`g` squarefree and coprime to `q'`, the part of S2 at `r/q + η` over the frequencies with
`gcd(k, q) = g` is small when `g > 1`, and within the same error of the principal model
when `g = 1`, as soon as the twisted prefix sums of hypothesis iv of Theorem 2 are at most
`M` for every character of every modulus dividing `q`. -/
theorem major_gcd_class512j (lo hi : ℕ) (b : ℕ → ℂ) (q g q' : ℕ) [NeZero q] [NeZero q']
    (hq : q = g * q') (hg : Squarefree g) (hcop : Nat.Coprime g q') (r : ℤ)
    (hr : IsUnit (r : ZMod q')) (w : ℂ) (M T : ℝ) (hT : (hi : ℝ) ≤ T)
    (hc : ∀ n : ℕ, n ∣ q → ∀ χ : DirichletCharacter ℂ n, ∀ t : ℝ, t ≤ T →
      ‖∑ k ∈ (Finset.Ioc lo hi).filter (fun k : ℕ => (k : ℝ) ≤ t),
        (b k * χ (k : ZMod n) - Thm2.delta χ * w)‖ ≤ M) (η : ℝ) :
    ‖(∑ k ∈ (Finset.Ioc lo hi).filter (fun k => Nat.gcd k q = g),
        b k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) -
      (if g = 1 then
        (q.totient : ℂ)⁻¹ * gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar * w *
          ∑ k ∈ Finset.Ioc lo hi, @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ)) else 0)‖ ≤
      Real.sqrt q' * (g.divisors.card : ℝ) *
        ((1 + 2 * Real.pi * |η| * ((hi - lo : ℕ) : ℝ)) * M) := by
  have hφ : (0 : ℝ) < (q'.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q'))
  have hgu : IsUnit (g : ZMod q') := (ZMod.isUnit_iff_coprime g q').mpr hcop
  have hX : (∑ k ∈ (Finset.Ioc lo hi).filter (fun k => Nat.gcd k q = g),
        b k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) =
      (q'.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q',
        gaussSum χ⁻¹ ZMod.stdAddChar * χ (r : ZMod q') * χ⁻¹ (g : ZMod q') *
          ∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : ℂ) *
            ∑ k ∈ Finset.Ioc lo hi, b k *
              (DirichletCharacter.changeLevel (Dvd.intro d rfl : q' ∣ q' * d) χ)
                (k : ZMod (q' * d)) *
                @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ)) := by
    rw [Finset.sum_filter]
    have hk : ∀ k ∈ Finset.Ioc lo hi,
        (if Nat.gcd k q = g then
          b k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ)) else 0) =
        b k * ((q'.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q',
          gaussSum χ⁻¹ ZMod.stdAddChar * χ (r : ZMod q') * χ⁻¹ (g : ZMod q') *
            ∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : ℂ) *
              ((DirichletCharacter.changeLevel (Dvd.intro d rfl : q' ∣ q' * d) χ)
                  (k : ZMod (q' * d)) *
                @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ)))) := by
      intro k _
      rw [← gcd_class_expansion512j g q' hg hcop r hr k η]
      have e1 : Nat.gcd k q = Nat.gcd k (g * q') := by rw [hq]
      have e2 : (q : ℝ) = ((g * q' : ℕ) : ℝ) := by rw [hq]
      rw [e1, e2]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl hk]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro χ _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hY : (if g = 1 then
        (q.totient : ℂ)⁻¹ * gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar * w *
          ∑ k ∈ Finset.Ioc lo hi, @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ)) else 0) =
      (q'.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q',
        gaussSum χ⁻¹ ZMod.stdAddChar * χ (r : ZMod q') * χ⁻¹ (g : ZMod q') *
          ∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : ℂ) *
            ∑ k ∈ Finset.Ioc lo hi, Thm2.delta χ * w *
                @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ)) := by
    rw [Finset.sum_eq_single (1 : DirichletCharacter ℂ q')]
    · rw [← Finset.sum_mul, sum_moebius512j, inv_one, MulChar.one_apply hr,
        MulChar.one_apply hgu]
      by_cases hg1 : g = 1
      · subst hg1
        have hqq : q' = q := by rw [hq, one_mul]
        subst hqq
        simp only [Thm2.delta, ↓reduceIte, ← Finset.mul_sum]
        ring
      · simp only [hg1, ↓reduceIte, zero_mul, mul_zero]
    · intro χ _ hχ
      simp [Thm2.delta, hχ]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  have hM : 0 ≤ M := (norm_nonneg _).trans (hc 1 (one_dvd q) 1 T le_rfl)
  rw [hX, hY, ← mul_sub, ← Finset.sum_sub_distrib]
  have hterm : ∀ χ : DirichletCharacter ℂ q',
      ‖gaussSum χ⁻¹ ZMod.stdAddChar * χ (r : ZMod q') * χ⁻¹ (g : ZMod q') *
          (∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : ℂ) *
            ∑ k ∈ Finset.Ioc lo hi, b k *
              (DirichletCharacter.changeLevel (Dvd.intro d rfl : q' ∣ q' * d) χ)
                (k : ZMod (q' * d)) *
                @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) -
        gaussSum χ⁻¹ ZMod.stdAddChar * χ (r : ZMod q') * χ⁻¹ (g : ZMod q') *
          ∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : ℂ) *
            ∑ k ∈ Finset.Ioc lo hi, Thm2.delta χ * w *
                @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))‖ ≤
        Real.sqrt q' * ((g.divisors.card : ℝ) *
          ((1 + 2 * Real.pi * |η| * ((hi - lo : ℕ) : ℝ)) * M)) := by
    intro χ
    have hcoef : ‖gaussSum χ⁻¹ ZMod.stdAddChar * χ (r : ZMod q') * χ⁻¹ (g : ZMod q')‖ ≤
        Real.sqrt q' := by
      rw [norm_mul, norm_mul]
      have h1 := gauss_norm512j χ⁻¹
      have h2 : ‖χ (r : ZMod q')‖ ≤ 1 := χ.norm_le_one _
      have h3 : ‖χ⁻¹ (g : ZMod q')‖ ≤ 1 := χ⁻¹.norm_le_one _
      calc _ ≤ Real.sqrt q' * 1 * 1 := by gcongr
        _ = _ := by ring
    rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul]
    refine mul_le_mul hcoef ?_ (norm_nonneg _) (Real.sqrt_nonneg _)
    calc _ ≤ ∑ d ∈ g.divisors, ‖(ArithmeticFunction.moebius d : ℂ) *
            (∑ k ∈ Finset.Ioc lo hi, b k *
              (DirichletCharacter.changeLevel (Dvd.intro d rfl : q' ∣ q' * d) χ)
                (k : ZMod (q' * d)) *
                @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))) -
          (ArithmeticFunction.moebius d : ℂ) *
            ∑ k ∈ Finset.Ioc lo hi, Thm2.delta χ * w *
                @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))‖ := norm_sum_le _ _
      _ ≤ ∑ _d ∈ g.divisors, (1 + 2 * Real.pi * |η| * ((hi - lo : ℕ) : ℝ)) * M := by
        apply Finset.sum_le_sum
        intro d hd
        have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
        have : NeZero (q' * d) := ⟨Nat.mul_ne_zero (NeZero.ne q') hd0⟩
        have hdq : q' * d ∣ q := by
          rw [hq, mul_comm]
          exact Nat.mul_dvd_mul_right (Nat.dvd_of_mem_divisors hd) q'
        have hδ : Thm2.delta
            (DirichletCharacter.changeLevel (Dvd.intro d rfl : q' ∣ q' * d) χ) =
              Thm2.delta χ := by
          by_cases hχ1 : χ = 1
          · subst hχ1
            simp [Thm2.delta]
          · have hne : DirichletCharacter.changeLevel (Dvd.intro d rfl : q' ∣ q' * d) χ ≠ 1 := by
              rwa [Ne, DirichletCharacter.changeLevel_eq_one_iff]
            simp [Thm2.delta, hχ1, hne]
        have hps := partial_summation512j lo hi
          (fun k => b k *
            (DirichletCharacter.changeLevel (Dvd.intro d rfl : q' ∣ q' * d) χ)
              (k : ZMod (q' * d)) -
            Thm2.delta (DirichletCharacter.changeLevel (Dvd.intro d rfl : q' ∣ q' * d) χ) * w)
          M T hT (hc (q' * d) hdq _) η
        rw [hδ] at hps
        have hμ : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_intCast]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul]
        simp only [← sub_mul]
        calc _ ≤ 1 * ((1 + 2 * Real.pi * |η| * ((hi - lo : ℕ) : ℝ)) * M) :=
              mul_le_mul hμ hps (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.univ : Finset (DirichletCharacter ℂ q')).card : ℝ) =
      (q'.totient : ℝ) := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q']
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q'.totient : ℝ)⁻¹ * ∑ _χ : DirichletCharacter ℂ q',
        Real.sqrt q' * ((g.divisors.card : ℝ) *
          ((1 + 2 * Real.pi * |η| * ((hi - lo : ℕ) : ℝ)) * M)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hφ.le)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => hterm χ)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard, ← mul_assoc, inv_mul_cancel₀ hφ.ne', one_mul]
      ring

/-- P0069 page 7, the S2 replacement after display 2.5: for a squarefree modulus `q` and
arbitrary coefficients `b`, with no coprimality condition, S2 at `r/q + η` differs from
the principal model by at most `√q τ(q)² (1 + 2π|η|(hi - lo)) M`, where `M` bounds the
twisted prefix sums of hypothesis iv of Theorem 2 for every character of every modulus
dividing `q`. -/
theorem major_squarefree512j (lo hi : ℕ) (b : ℕ → ℂ) {q : ℕ} [NeZero q] (hq : Squarefree q)
    (r : ℤ) (hr : IsUnit (r : ZMod q)) (w : ℂ) (M T : ℝ) (hT : (hi : ℝ) ≤ T)
    (hc : ∀ n : ℕ, n ∣ q → ∀ χ : DirichletCharacter ℂ n, ∀ t : ℝ, t ≤ T →
      ‖∑ k ∈ (Finset.Ioc lo hi).filter (fun k : ℕ => (k : ℝ) ≤ t),
        (b k * χ (k : ZMod n) - Thm2.delta χ * w)‖ ≤ M) (η : ℝ) :
    ‖(∑ k ∈ Finset.Ioc lo hi,
        b k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) -
      (q.totient : ℂ)⁻¹ * gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar * w *
        ∑ k ∈ Finset.Ioc lo hi, @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ))‖ ≤
      Real.sqrt q * (q.divisors.card : ℝ) ^ 2 *
        ((1 + 2 * Real.pi * |η| * ((hi - lo : ℕ) : ℝ)) * M) := by
  have hq0 : q ≠ 0 := NeZero.ne q
  have hM : 0 ≤ M := (norm_nonneg _).trans (hc 1 (one_dvd q) 1 T le_rfl)
  have hbound : 0 ≤ (1 + 2 * Real.pi * |η| * ((hi - lo : ℕ) : ℝ)) * M :=
    mul_nonneg (by positivity) hM
  have key : (∑ k ∈ Finset.Ioc lo hi,
        b k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) -
      (q.totient : ℂ)⁻¹ * gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar * w *
        ∑ k ∈ Finset.Ioc lo hi, @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ)) =
      ∑ g ∈ q.divisors, ((∑ k ∈ (Finset.Ioc lo hi).filter (fun k => Nat.gcd k q = g),
          b k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) -
        (if g = 1 then
          (q.totient : ℂ)⁻¹ * gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar * w *
            ∑ k ∈ Finset.Ioc lo hi, @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ)) else 0)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' q.divisors 1,
      ite_eq_left (Nat.one_mem_divisors.mpr hq0),
      Finset.sum_fiberwise_of_maps_to (fun k _ =>
        Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right k q, hq0⟩)]
  rw [key]
  calc
    _ ≤ ∑ g ∈ q.divisors, ‖(∑ k ∈ (Finset.Ioc lo hi).filter (fun k => Nat.gcd k q = g),
          b k * @fourier 1 (k : ℤ) (((r : ℝ) / q + η : ℝ) : AddCircle (1 : ℝ))) -
        (if g = 1 then
          (q.totient : ℂ)⁻¹ * gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar * w *
            ∑ k ∈ Finset.Ioc lo hi, @fourier 1 (k : ℤ) (η : AddCircle (1 : ℝ)) else 0)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _g ∈ q.divisors, Real.sqrt q * (q.divisors.card : ℝ) *
        ((1 + 2 * Real.pi * |η| * ((hi - lo : ℕ) : ℝ)) * M) := by
      apply Finset.sum_le_sum
      intro g hg
      obtain ⟨q', hq'⟩ := Nat.dvd_of_mem_divisors hg
      have hq'0 : q' ≠ 0 := by
        rintro rfl
        exact hq0 (by rw [hq', mul_zero])
      have : NeZero q' := ⟨hq'0⟩
      have hsq : Squarefree (g * q') := by
        rw [← hq']
        exact hq
      have hq'q : q' ∣ q := Dvd.intro_left g hq'.symm
      have hr' : IsUnit (r : ZMod q') := by
        have h := hr.map (ZMod.castHom hq'q (ZMod q'))
        rwa [map_intCast] at h
      have h := major_gcd_class512j lo hi b q g q' hq' hsq.of_mul_left
        (Nat.coprime_of_squarefree_mul hsq) r hr' w M T hT hc η
      refine h.trans ?_
      have h1 : Real.sqrt q' ≤ Real.sqrt q :=
        Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) hq'q)
      have h2 : (g.divisors.card : ℝ) ≤ (q.divisors.card : ℝ) := by
        exact_mod_cast Finset.card_le_card
          (Nat.divisors_subset_of_dvd hq0 (Nat.dvd_of_mem_divisors hg))
      gcongr
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

private lemma dvd_val_iff512j {q d : ℕ} [NeZero q] (hd : d ∣ q) (a : ZMod q) :
    d ∣ a.val ↔ ZMod.castHom hd (ZMod d) a = 0 := by
  rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff]

private lemma subgroup_sum512j {q d : ℕ} [NeZero q] (hd : d ∣ q) :
    ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => d ∣ a.val), ZMod.stdAddChar a =
      if d = q then (1 : ℂ) else 0 := by
  by_cases hdq : d = q
  · subst hdq
    rw [ite_eq_left rfl, Finset.sum_eq_single (0 : ZMod d)]
    · simp
    · intro a ha ha0
      exfalso
      apply ha0
      have h1 := (Finset.mem_filter.mp ha).2
      have h2 := ZMod.val_lt a
      exact (ZMod.val_eq_zero a).mp (Nat.eq_zero_of_dvd_of_lt h1 h2)
    · intro h
      exfalso
      apply h
      simp
  · rw [ite_eq_right hdq]
    have hmem : ∀ a : ZMod q,
        a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => d ∣ a.val) ↔
          a + (d : ZMod q) ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => d ∣ a.val) := by
      intro a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, dvd_val_iff512j hd, map_add,
        map_natCast, ZMod.natCast_self, add_zero]
    have hshift : ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => d ∣ a.val),
          ZMod.stdAddChar a =
        ZMod.stdAddChar (d : ZMod q) *
          ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => d ∣ a.val),
            (ZMod.stdAddChar a : ℂ) := by
      rw [Finset.mul_sum]
      calc
        _ = ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => d ∣ a.val),
            (ZMod.stdAddChar (a + (d : ZMod q)) : ℂ) :=
          (Finset.sum_equiv (Equiv.addRight (d : ZMod q)) (by intro a; simpa using hmem a)
            (by intro a _; simp)).symm
        _ = _ := Finset.sum_congr rfl fun a _ => by rw [AddChar.map_add_eq_mul, mul_comm]
    have hne : ZMod.stdAddChar (d : ZMod q) ≠ (1 : ℂ) := by
      intro h
      have h0 : (d : ZMod q) = 0 :=
        ZMod.injective_stdAddChar (by rw [h, AddChar.map_zero_eq_one])
      rw [ZMod.natCast_eq_zero_iff] at h0
      exact hdq (Nat.dvd_antisymm hd h0)
    have hz : (1 - ZMod.stdAddChar (d : ZMod q)) *
        ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => d ∣ a.val),
          (ZMod.stdAddChar a : ℂ) = 0 := by
      rw [sub_mul, one_mul, ← hshift, sub_self]
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact h

/-- P0069 page 6 display 2.1, second formula: the Gauss sum of the principal character
modulo `q` is the Moebius function of `q`, for every modulus. This is the coefficient of
the principal model on page 7, and it vanishes when `q` is not squarefree. -/
theorem gauss_principal512j (q : ℕ) [NeZero q] :
    gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar =
      (ArithmeticFunction.moebius q : ℂ) := by
  have hq0 : q ≠ 0 := NeZero.ne q
  have h1 : ∀ a : ZMod q, (1 : DirichletCharacter ℂ q) a =
      ∑ d ∈ q.divisors, if d ∣ a.val then (ArithmeticFunction.moebius d : ℂ) else 0 := by
    intro a
    have hfilter : q.divisors.filter (fun d => d ∣ a.val) = (Nat.gcd a.val q).divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨hdq, _⟩, hda⟩
        exact ⟨⟨hda, hdq⟩, Nat.gcd_ne_zero_right hq0⟩
      · rintro ⟨⟨hda, hdq⟩, _⟩
        exact ⟨⟨hdq, hq0⟩, hda⟩
    rw [← Finset.sum_filter, hfilter, sum_moebius512j]
    have hu : IsUnit a ↔ Nat.gcd a.val q = 1 := by
      conv_lhs => rw [← ZMod.natCast_zmod_val a]
      exact ZMod.isUnit_iff_coprime a.val q
    by_cases h : IsUnit a
    · rw [MulChar.one_apply h, ite_eq_left (hu.mp h)]
    · rw [MulChar.map_nonunit _ h, ite_eq_right (fun h' => h (hu.mpr h'))]
  unfold gaussSum
  simp_rw [h1, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h2 : ∀ d ∈ q.divisors,
      ∑ a : ZMod q, (if d ∣ a.val then (ArithmeticFunction.moebius d : ℂ) else 0) *
        ZMod.stdAddChar a = if d = q then (ArithmeticFunction.moebius d : ℂ) else 0 := by
    intro d hd
    have h3 := subgroup_sum512j (Nat.dvd_of_mem_divisors hd)
    calc
      _ = (ArithmeticFunction.moebius d : ℂ) *
          ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter (fun a => d ∣ a.val),
            (ZMod.stdAddChar a : ℂ) := by
        rw [Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro a _
        split_ifs <;> ring
      _ = _ := by
        rw [h3]
        split_ifs <;> simp
  rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq', ite_eq_left (Nat.mem_divisors_self q hq0)]

end LeanLab.BHP1997.Route512Major
