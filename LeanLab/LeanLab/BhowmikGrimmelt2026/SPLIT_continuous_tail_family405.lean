/-
A split of the continuous tail family bound into three leaves plus an assembly.

The major arc integral for the continuous tail is partitioned by frequency region:
the arcs of denominator one, where the nearest integer representative is the selected
rational, and the remaining major arcs, where the selected rational has denominator at
least two. The leaves are (1) the reduction of the coefficient to the sum of the two
region pieces, (2) the family bound on the denominator one region, and (3) the family
bound on the remaining major arcs. The assembly combines them with the two term split
of a finite family of squared norms and the absorption of the logarithm power.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp405a

namespace LeanLab.BhowmikGrimmelt2026

open MeasureTheory
open scoped FourierTransform

/-- The pair count times the rapid decay is a fixed power of the length. -/
private theorem rpow_scale405 {X : ℝ} (hX : 0 < X) {ϑ : ℝ} (hϑ : 0 < ϑ) :
    ((X ^ ϑ) ^ 2) * (5 * X ^ ϑ) ^ (-(2 + 2 / ϑ)) = 5 ^ (-(2 + 2 / ϑ)) * X ^ (-2 : ℝ) := by
  have hR0 : 0 ≤ X ^ ϑ := (Real.rpow_pos_of_pos hX ϑ).le
  have hR : 0 < X ^ ϑ := Real.rpow_pos_of_pos hX ϑ
  have hcomb : (X ^ ϑ) ^ 2 * (X ^ ϑ) ^ (-(2 + 2 / ϑ)) = X ^ (-2 : ℝ) := by
    rw [← Real.rpow_two, ← Real.rpow_add hR]
    have hexp : (2 : ℝ) + -(2 + 2 / ϑ) = -(2 / ϑ) := by
      field_simp
      ring
    rw [hexp, ← Real.rpow_mul hX.le]
    have hexp2 : ϑ * -(2 / ϑ) = -2 := by
      field_simp
    rw [hexp2]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5) hR0]
  calc (X ^ ϑ) ^ 2 * (5 ^ (-(2 + 2 / ϑ)) * (X ^ ϑ) ^ (-(2 + 2 / ϑ)))
      = 5 ^ (-(2 + 2 / ϑ)) * ((X ^ ϑ) ^ 2 * (X ^ ϑ) ^ (-(2 + 2 / ϑ))) := by ring
    _ = 5 ^ (-(2 + 2 / ϑ)) * X ^ (-2 : ℝ) := by rw [hcomb]

/-- The inverse square of the length is paid by the fourth power of the smoothing scale. -/
private theorem rpow_bound_eta405 {X : ℝ} (hX : 0 < X) (hX1 : 1 ≤ X) {ϑ η : ℝ} (hϑ : 0 < ϑ)
    (hscale : 10 * (X ^ ϑ) ^ 2 ≤ η * X) : X ^ (-2 : ℝ) ≤ 100 * η ^ 2 := by
  have h2 : (X ^ ϑ) ^ 2 = X ^ (2 * ϑ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hX.le]
    congr 1
    ring
  rw [h2] at hscale
  have hlow : X ^ (2 * ϑ - 1) ≤ η / 10 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 10)]
    have hstep : 10 * X ^ (2 * ϑ) / X ≤ η := (div_le_iff₀ hX).mpr hscale
    have hstep2 : 10 * X ^ (2 * ϑ) / X = 10 * X ^ (2 * ϑ - 1) := by
      rw [mul_div_assoc, ← Real.rpow_sub_one hX.ne' (2 * ϑ)]
    rw [hstep2] at hstep
    linarith
  have hsq : (X ^ (2 * ϑ - 1)) ^ 2 ≤ (η / 10) ^ 2 := by
    apply pow_le_pow_left₀ (Real.rpow_nonneg hX.le _) hlow
  have he : (X ^ (2 * ϑ - 1)) ^ 2 = X ^ (4 * ϑ - 2) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hX.le]
    congr 1
    ring
  rw [he] at hsq
  have h4 : (1 : ℝ) ≤ X ^ (4 * ϑ) := by
    have h6 : X ^ (4 * ϑ) = (X ^ 4) ^ ϑ := by
      rw [← Real.rpow_natCast (x := X) 4, ← Real.rpow_mul hX.le]
      norm_num
    rw [h6]
    have h7 : (1 : ℝ) ≤ X ^ 4 := by
      simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hX1 4
    exact Real.one_le_rpow h7 hϑ.le
  have hsplit : X ^ (-2 : ℝ) = X ^ (4 * ϑ - 2) / X ^ (4 * ϑ) := by
    rw [← Real.rpow_sub hX]
    congr 1
    ring
  rw [hsplit]
  have hle : X ^ (4 * ϑ - 2) / X ^ (4 * ϑ) ≤ X ^ (4 * ϑ - 2) :=
    div_le_self (Real.rpow_nonneg hX.le _) h4
  have hfin : (η / 10) ^ 2 = η ^ 2 / 100 := by ring
  rw [hfin] at hsq
  nlinarith [sq_nonneg η]



/-- A non-integer reduced fraction is at least one over its denominator from every integer. -/
private theorem le_abs_rat_sub_int405 {q a : ℕ} {m : ℤ} (hq : 0 < q) (ha : 0 < a) (haq : a < q) :
    (1 : ℝ) / q ≤ |(a : ℝ) / q - (m : ℝ)| := by
  have hqp : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hne : (a : ℤ) - m * (q : ℤ) ≠ 0 := by
    intro h
    have hdvd : (q : ℤ) ∣ (a : ℤ) := ⟨m, by linarith [h]⟩
    have hdvdN : q ∣ a := by exact_mod_cast hdvd
    have hle : q ≤ a := Nat.le_of_dvd ha hdvdN
    omega
  have h1 : (1 : ℝ) ≤ |(a : ℝ) - (m : ℝ) * (q : ℝ)| := by
    have hz := Int.one_le_abs hne
    have hcast : |(a : ℤ) - m * (q : ℤ)| = |(a : ℝ) - (m : ℝ) * (q : ℝ)| := by
      push_cast
      rfl
    rw [← hcast]
    exact_mod_cast hz
  have heq : (a : ℝ) / q - (m : ℝ) = ((a : ℝ) - (m : ℝ) * (q : ℝ)) / q := by
    field_simp
  rw [heq, abs_div, abs_of_pos hqp]
  exact (div_le_div_iff_of_pos_right hqp).mpr h1

/-- Off a reduced fraction with denominator at least two, the distance to the nearest
integer stays comparable with the denominator once the frequency is near an integer. -/
private theorem intDist_rat_lower405 {q a : ℕ} {α δ : ℝ} (hq : 0 < q) (ha : 0 < a) (haq : a < q)
    (hδ : |α - ((round α : ℤ) : ℝ)| ≤ δ) (hδq : δ ≤ 1 / (2 * (q : ℝ))) :
    1 / (2 * (q : ℝ)) ≤ intDist (α - (a : ℝ) / q) := by
  have hqp : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [intDist]
  have h1 : (1 : ℝ) / q ≤ |(a : ℝ) / q - (((round α - round (α - (a : ℝ) / q)) : ℤ) : ℝ)| :=
    le_abs_rat_sub_int405 hq ha haq
  have htri : |(a : ℝ) / q - (((round α - round (α - (a : ℝ) / q)) : ℤ) : ℝ)| ≤
      |(α - (a : ℝ) / q) - ((round (α - (a : ℝ) / q) : ℤ) : ℝ)| +
        |α - ((round α : ℤ) : ℝ)| := by
    have heq : (a : ℝ) / q - (((round α - round (α - (a : ℝ) / q)) : ℤ) : ℝ) =
        -((α - (a : ℝ) / q) - ((round (α - (a : ℝ) / q) : ℤ) : ℝ)) +
          (α - ((round α : ℤ) : ℝ)) := by
      push_cast
      ring
    rw [heq]
    have h := abs_add_le (-((α - (a : ℝ) / q) - ((round (α - (a : ℝ) / q) : ℤ) : ℝ)))
      (α - ((round α : ℤ) : ℝ))
    simpa only [abs_neg] using h
  have key : (1 : ℝ) / q - |α - ((round α : ℤ) : ℝ)| ≤
      |(α - (a : ℝ) / q) - ((round (α - (a : ℝ) / q) : ℤ) : ℝ)| := by linarith
  have hhalf : (1 : ℝ) / (2 * (q : ℝ)) = 1 / q - 1 / (2 * (q : ℝ)) := by
    field_simp
    ring
  rw [hhalf]
  linarith [hδ, hδq]

/-- On the arcs whose nearest integer is the selected rational the discrete central
transform and the full reduced pair sum differ only in the pairs of denominator at
least two, and those decay faster than any power of the length. -/
private theorem near_bRhat_den_one405 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      |α - ((round α : ℤ) : ℝ)| ≤ (X : ℝ) ^ ϑ / (X : ℝ) → MajorArc X ((X : ℝ) ^ ϑ) α →
      ‖nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
        bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α‖ ≤ B * η ^ 2 := by
  classical
  obtain ⟨Cg, hCg, hGt⟩ := GThat_bound hG.supp hG.smooth (2 + 2 / ϑ)
  refine ⟨2 * Cg * 5 ^ (-(2 + 2 / ϑ)) * 100, by positivity, ?_⟩
  intro X hX η hη hη1 hscale α hαI hδ hm
  let R : ℝ := (X : ℝ) ^ ϑ
  let T : ℕ → ℝ := fun q => η * X * q / R
  have hXp : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 1 ≤ X)
  have hRp : 0 < R := Real.rpow_pos_of_pos hXp ϑ
  have hR0 : 0 ≤ R := hRp.le
  have hR1 : 1 ≤ R := Real.one_le_rpow hX1 hϑ.le
  have hηX : η * (X : ℝ) ≤ (X : ℝ) := by nlinarith
  have hsep : 2 * R ^ 2 < (X : ℝ) := by
    have h2 : 10 * R ^ 2 ≤ (X : ℝ) := by linarith
    nlinarith
  have hRX : R ≤ (X : ℝ) := by nlinarith [hR1, sq_nonneg (R - 1)]
  have hTpos : ∀ q ∈ Finset.Icc 1 ⌊R⌋₊, 0 < T q := by
    intro q hq
    have hq1 : 0 < q := by have := (Finset.mem_Icc.mp hq).1; omega
    have hqp : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
    dsimp [T, R]
    positivity
  have hM1 : 1 ≤ ⌊R⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hR1)
  -- the selected rational is the nearest integer
  obtain ⟨q, hqmem, a, hamem, hclose⟩ := majorArc_center_in_sum328 hXp hRX hαI hm
  have hqpos : 0 < q := by have := (Finset.mem_Icc.mp hqmem).1; omega
  have hcop : Int.gcd a q = 1 := (Finset.mem_filter.mp hamem).2
  have huniq := near_rational_unique328 (X := (X : ℝ)) (R := R) (α := α) hXp hR0 hsep
    (q := q) (r := 1) (a := a) (b := round α) hqpos (by norm_num)
    ((Nat.cast_le.mpr (Finset.mem_Icc.mp hqmem).2).trans (Nat.floor_le hR0))
    (by simpa using hR1) hcop (by norm_num) hclose (by simpa using hδ)
  obtain ⟨hqn, han⟩ := huniq
  subst hqn
  subst han
  -- the central transform is the denominator one term
  have hnear : nearTransform328 G X R η α = GThat G (T 1) α := by
    have h := nearTransform_eq328 (G := G) (X := X) (R := R) (η := η) (α := α) hXp hR0 hsep
      (q := 1) hqmem hamem hclose
    simp only [Nat.cast_one, div_one] at h
    have hT1eq : T 1 = η * X * 1 / R := by simp [T]
    rw [h, hT1eq]
    exact GThat_center G (η * X * 1 / R) α
  have hp0 : (⟨1, 0⟩ : Σ _ : ℕ, ℕ) ∈ reducedPairs ⌊R⌋₊ := by
    rw [mem_reducedPairs]
    exact ⟨le_rfl, hM1, by norm_num, by simp⟩
  have hbr1 : bRhat G R T α = ∑ p ∈ reducedPairs ⌊R⌋₊, GThat G (T p.1) (α - (p.2 : ℝ) / p.1) := by
    rw [bRhat_eq hG.supp hG.even R T hTpos α, ← sum_reducedPairs]
  have hbr2 : bRhat G R T α = GThat G (T 1) α +
      ∑ p ∈ (reducedPairs ⌊R⌋₊).erase ⟨1, 0⟩, GThat G (T p.1) (α - (p.2 : ℝ) / p.1) := by
    rw [hbr1, ← Finset.add_sum_erase _ _ hp0]
    norm_num
  have hterm : ∀ p ∈ (reducedPairs ⌊R⌋₊).erase ⟨1, 0⟩,
      ‖GThat G (T p.1) (α - (p.2 : ℝ) / p.1)‖ ≤ 2 * Cg * (5 * R) ^ (-(2 + 2 / ϑ)) := by
    intro p hp
    obtain ⟨hq1, hqM, haq, hc⟩ := (mem_reducedPairs _ p).mp (Finset.mem_of_mem_erase hp)
    have hne : p ≠ ⟨1, 0⟩ := Finset.ne_of_mem_erase hp
    have hq2 : 2 ≤ p.1 := by
      rcases Nat.lt_or_ge p.1 2 with h | h
      · have h1 : p.1 = 1 := by omega
        have h2 : p.2 = 0 := by omega
        exact absurd (Sigma.ext h1 (by simpa using h2)) hne
      · exact h
    have hqp : (0 : ℝ) < (p.1 : ℝ) := by
      have : 0 < p.1 := by omega
      exact_mod_cast this
    have ha0 : 0 < p.2 := by
      rcases Nat.eq_zero_or_pos p.2 with h | h
      · exfalso
        rw [h] at hc
        have : p.1 = 1 := by simpa using hc
        omega
      · exact h
    have hδq : R / (X : ℝ) ≤ 1 / (2 * (p.1 : ℝ)) := by
      have hqR : (p.1 : ℝ) ≤ R := (Nat.cast_le.mpr hqM).trans (Nat.floor_le hR0)
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * (p.1 : ℝ))]
      rw [div_mul_eq_mul_div]
      refine (div_le_one (by positivity : (0:ℝ) < (X : ℝ))).mpr ?_
      nlinarith [hsep, hRp, hqp, hqR]
    have hlow : 1 / (2 * (p.1 : ℝ)) ≤ intDist (α - (p.2 : ℝ) / p.1) :=
      intDist_rat_lower405 (by omega : 0 < p.1) ha0 haq (by simpa using hδ) hδq
    have hTform : T p.1 = η * X * (p.1 : ℝ) / R := rfl
    have hp1 : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast (by omega : 1 ≤ p.1)
    have hTlow : 5 * R ≤ T p.1 := by
      rw [hTform]
      rw [le_div_iff₀ hRp]
      nlinarith [hscale, hqp, hRp, hp1]
    have hT1 : 1 ≤ T p.1 := by linarith [hR1]
    have hgap : 5 * R ≤ T p.1 * intDist (α - (p.2 : ℝ) / p.1) := by
      have h1 : T p.1 * (1 / (2 * (p.1 : ℝ))) ≤ T p.1 * intDist (α - (p.2 : ℝ) / p.1) :=
        mul_le_mul_of_nonneg_left hlow (by positivity)
      have h2 : 5 * R ≤ T p.1 * (1 / (2 * (p.1 : ℝ))) := by
        rw [hTform]
        have hp1 : (0 : ℝ) < (p.1 : ℝ) := hqp
        field_simp
        nlinarith [hscale, hRp, hp1, hR1]
      linarith
    have hb := hGt (T p.1) (α - (p.2 : ℝ) / p.1) hT1
    have hs1 : (1 + T p.1 * intDist (α - (p.2 : ℝ) / p.1)) ^ (-(2 + 2 / ϑ)) ≤
        (5 * R) ^ (-(2 + 2 / ϑ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ) < 5 * R) (by linarith)
        (by
          have hp : (0:ℝ) < 2 / ϑ := by positivity
          linarith : -(2 + 2 / ϑ) ≤ 0)
    have hs2 : (T p.1) ^ (-(2 + 2 / ϑ)) ≤ (5 * R) ^ (-(2 + 2 / ϑ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ) < 5 * R) (by linarith)
        (by
          have hp : (0:ℝ) < 2 / ϑ := by positivity
          linarith : -(2 + 2 / ϑ) ≤ 0)
    calc ‖GThat G (T p.1) (α - (p.2 : ℝ) / p.1)‖
        ≤ Cg * ((1 + T p.1 * intDist (α - (p.2 : ℝ) / p.1)) ^ (-(2 + 2 / ϑ)) +
            (T p.1) ^ (-(2 + 2 / ϑ))) := hb
      _ ≤ Cg * ((5 * R) ^ (-(2 + 2 / ϑ)) + (5 * R) ^ (-(2 + 2 / ϑ))) := by
        apply mul_le_mul_of_nonneg_left _ hCg.le
        linarith
      _ = 2 * Cg * (5 * R) ^ (-(2 + 2 / ϑ)) := by ring
  -- sum the remaining pairs
  have hcard : (((reducedPairs ⌊R⌋₊).erase ⟨1, 0⟩).card : ℝ) ≤ R ^ 2 := by
    have h1 : ((reducedPairs ⌊R⌋₊).card : ℝ) ≤ (⌊R⌋₊ : ℝ) ^ 2 := by
      exact_mod_cast reducedPairs_card_le ⌊R⌋₊
    have h2 : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le hR0
    have h3 : ((⌊R⌋₊ : ℝ)) ^ 2 ≤ R ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) h2
    have h4 : (((reducedPairs ⌊R⌋₊).erase ⟨1, 0⟩).card : ℝ) ≤ ((reducedPairs ⌊R⌋₊).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.erase_subset _ _)
    linarith
  have hsum : ‖∑ p ∈ (reducedPairs ⌊R⌋₊).erase ⟨1, 0⟩,
      GThat G (T p.1) (α - (p.2 : ℝ) / p.1)‖ ≤
      R ^ 2 * (2 * Cg * (5 * R) ^ (-(2 + 2 / ϑ))) := by
    have h := norm_sum_le_card_mul _ _ hterm
    have h2 := mul_le_mul_of_nonneg_right hcard (by positivity : (0:ℝ) ≤ 2 * Cg * (5 * R) ^ (-(2 + 2 / ϑ)))
    linarith
  have hpow : R ^ 2 * (5 * R) ^ (-(2 + 2 / ϑ)) = 5 ^ (-(2 + 2 / ϑ)) * (X : ℝ) ^ (-2 : ℝ) :=
    rpow_scale405 hXp hϑ
  have hXm2 : (X : ℝ) ^ (-2 : ℝ) ≤ 100 * η ^ 2 := rpow_bound_eta405 hXp hX1 hϑ hscale
  calc ‖nearTransform328 G X R η α - bRhat G R T α‖
      = ‖∑ p ∈ (reducedPairs ⌊R⌋₊).erase ⟨1, 0⟩, GThat G (T p.1) (α - (p.2 : ℝ) / p.1)‖ := by
        rw [hnear, hbr2]
        have hid : GThat G (T 1) α - (GThat G (T 1) α +
            ∑ p ∈ (reducedPairs ⌊R⌋₊).erase ⟨1, 0⟩, GThat G (T p.1) (α - (p.2 : ℝ) / p.1)) =
            -(∑ p ∈ (reducedPairs ⌊R⌋₊).erase ⟨1, 0⟩, GThat G (T p.1) (α - (p.2 : ℝ) / p.1)) := by
          ring
        rw [hid, norm_neg]
    _ ≤ R ^ 2 * (2 * Cg * (5 * R) ^ (-(2 + 2 / ϑ))) := hsum
    _ = 2 * Cg * (R ^ 2 * (5 * R) ^ (-(2 + 2 / ϑ))) := by ring
    _ = 2 * Cg * (5 ^ (-(2 + 2 / ϑ)) * (X : ℝ) ^ (-2 : ℝ)) := by rw [hpow]
    _ ≤ 2 * Cg * (5 ^ (-(2 + 2 / ϑ)) * (100 * η ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hXm2 (by positivity)
    _ = (2 * Cg * 5 ^ (-(2 + 2 / ϑ)) * 100) * η ^ 2 := by ring



/-- The full continuous rational model and the discrete central transform differ by order
eta squared on the denominator one arcs. -/
private theorem near_model_den_one_bound405 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      |α - ((round α : ℤ) : ℝ)| ≤ (X : ℝ) ^ ϑ / (X : ℝ) → MajorArc X ((X : ℝ) ^ ϑ) α →
      ‖nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
        continuousModel405 G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α‖ ≤ B * η ^ 2 := by
  obtain ⟨B₁, hB₁, h₁⟩ := near_bRhat_den_one405 hG ϑ hϑ
  obtain ⟨D, hD, h₂⟩ := alias_multiplier405 hG ϑ hϑ
  refine ⟨B₁ + D, by positivity, fun X hX η hη hη1 hscale α hαI hδ hm => ?_⟩
  have ha := h₁ X hX η hη hη1 hscale α hαI hδ hm
  have hb := h₂ X hX η hη hscale α
  have hEq : nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
      continuousModel405 G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α =
      (nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
        bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α) +
      (bRhat G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α -
        continuousModel405 G ((X : ℝ) ^ ϑ) (fun q => η * X * q / (X : ℝ) ^ ϑ) α) := by
    ring
  rw [hEq]
  calc ‖_ + _‖ ≤ _ + _ := norm_add_le _ _
    _ ≤ B₁ * η ^ 2 + D * η ^ 2 := add_le_add ha hb
    _ = (B₁ + D) * η ^ 2 := by ring

/-- The zero Poisson translate is uniformly bounded in scale and frequency. -/
private theorem centeredFourier_bound405 {G : ℝ → ℝ} (hG : IsMajorWeight G) :
    ∃ C : ℝ, 0 < C ∧ ∀ T β : ℝ, ‖centeredFourier405 G T β‖ ≤ C := by
  obtain ⟨C, hC, hF⟩ := fourier_decay hG.supp hG.smooth 1
  refine ⟨C, hC, fun T β => ?_⟩
  have h := hF (-T * (β - round β))
  rw [centeredFourier405]
  refine h.trans ?_
  have h1 : (1 : ℝ) ≤ 1 + |(-T * (β - round β))| := by linarith [abs_nonneg (-T * (β - round β))]
  have h2 : (1 + |(-T * (β - round β))|) ^ (-(1 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num)
  calc C * (1 + |(-T * (β - round β))|) ^ (-(1 : ℝ)) ≤ C * 1 :=
        mul_le_mul_of_nonneg_left h2 hC.le
    _ = C := by ring

/-- The finite centered continuous rational model is uniformly bounded in frequency. -/
private theorem continuousModel_bound405 {G : ℝ → ℝ} (hG : IsMajorWeight G)
    (R : ℝ) (T : ℕ → ℝ) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ α, ‖continuousModel405 G R T α‖ ≤ Cc := by
  classical
  obtain ⟨C, hC, hb⟩ := centeredFourier_bound405 hG
  refine ⟨C * ⌊R⌋₊ ^ 2, by positivity, fun α => ?_⟩
  have hInner : ∀ q ∈ Finset.Icc 1 ⌊R⌋₊,
      ‖∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        centeredFourier405 G (T q) (α - a / q)‖ ≤ (⌊R⌋₊ : ℝ) * C := by
    intro q hq
    calc ‖∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          centeredFourier405 G (T q) (α - a / q)‖
        ≤ (((Finset.range q).filter (fun a => Nat.Coprime a q)).card : ℝ) * C := by
          apply norm_sum_le_card_mul
          intro a ha
          exact hb (T q) (α - a / q)
      _ ≤ ((Finset.range q).card : ℝ) * C := by
          apply mul_le_mul_of_nonneg_right _ hC.le
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ = (q : ℝ) * C := by rw [Finset.card_range]
      _ ≤ (⌊R⌋₊ : ℝ) * C := by
          apply mul_le_mul_of_nonneg_right _ hC.le
          exact_mod_cast (Finset.mem_Icc.mp hq).2
  rw [continuousModel405]
  calc ‖∑ q ∈ Finset.Icc 1 ⌊R⌋₊, ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        centeredFourier405 G (T q) (α - a / q)‖
      ≤ ((Finset.Icc 1 ⌊R⌋₊).card : ℝ) * ((⌊R⌋₊ : ℝ) * C) := by
        apply norm_sum_le_card_mul
        intro q hq
        exact hInner q hq
    _ = C * ⌊R⌋₊ ^ 2 := by
        rw [Nat.card_Icc]
        have h2 : ((⌊R⌋₊ + 1 - 1 : ℕ) : ℝ) = (⌊R⌋₊ : ℝ) := by norm_num
        rw [h2]
        ring

/-- A masked product with a continuous exponential is interval integrable once the
multiplier times the smoothed square is square integrable. -/
private theorem masked_intervalIntegrable405 {ϕ : ℝ → ℝ} {W : ℝ → ℂ} {N : ℕ} {s : Set ℝ}
    (hs : MeasurableSet s)
    (hW : MemLp (fun α => Sphi ϕ N α ^ 2 * W α) 2 (volume.restrict (Set.Ioc 0 1))) :
    IntervalIntegrable (fun α => s.indicator
      (fun α => Sphi ϕ N α ^ 2 * W α * ee (-(N * α))) α) volume 0 1 := by
  have he : Continuous (fun α : ℝ => ee (-(N * α))) :=
    ee_contDiff.continuous.comp ((continuous_const.mul continuous_id).neg)
  have hi : IntervalIntegrable (fun α => Sphi ϕ N α ^ 2 * W α * ee (-(N * α))) volume 0 1 :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (hW.integrable (by norm_num : (1 : ENNReal) ≤ 2))).mul_continuousOn he.continuousOn
  exact ⟨hi.1.indicator hs, hi.2.indicator hs⟩


/-- LEAF. Step 1, the reduction: the continuous tail coefficient is exactly the sum of
its two frequency region pieces, the major arcs whose centre is an integer and the
remaining major arcs. This is the indicator identity for the major arc set together with
the interval integrability of both pieces; no estimate enters it. -/
theorem leaf_region_split405 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    {X : ℕ} (hX : 2 ≤ X) (N : ℕ) (ϑ : ℝ) (hϑ : 0 < ϑ) {η : ℝ} (hη : 0 < η) :
    continuousTail405 ϕ G X N ϑ η =
      (∫ α in (0 : ℝ)..1,
        ({α : ℝ | MajorArc X ((X : ℝ) ^ ϑ) α} ∩
          {α : ℝ | |α - ((round α : ℤ) : ℝ)| ≤ (X : ℝ) ^ ϑ / (X : ℝ)}).indicator
          (fun α => Sphi ϕ N α ^ 2 *
            (nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
              continuousModel405 G ((X : ℝ) ^ ϑ)
                (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))) α) +
      (∫ α in (0 : ℝ)..1,
        ({α : ℝ | MajorArc X ((X : ℝ) ^ ϑ) α} ∩
          {α : ℝ | |α - ((round α : ℤ) : ℝ)| ≤ (X : ℝ) ^ ϑ / (X : ℝ)}ᶜ).indicator
          (fun α => Sphi ϕ N α ^ 2 *
            (nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
              continuousModel405 G ((X : ℝ) ^ ϑ)
                (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))) α) := by
  classical
  let R : ℝ := (X : ℝ) ^ ϑ
  let T : ℕ → ℝ := fun q => η * X * q / R
  let A : Set ℝ := {α : ℝ | MajorArc X R α}
  let I : Set ℝ := {α : ℝ | |α - ((round α : ℤ) : ℝ)| ≤ R / (X : ℝ)}
  let g : ℝ → ℂ := fun α => Sphi ϕ N α ^ 2 *
    (nearTransform328 G X R η α - continuousModel405 G R T α) * ee (-(N * α))
  have hXp : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hRp : 0 < R := Real.rpow_pos_of_pos hXp ϑ
  have hA : MeasurableSet A := measurableSet_majorArc84 X R
  have hI : MeasurableSet I := by
    have hr : Measurable (fun β : ℝ => ((round β : ℤ) : ℝ)) := by
      have hr' : Measurable (fun β : ℝ => round β) := by
        simp_rw [round_eq]
        exact (measurable_id.add_const (1 / 2 : ℝ)).floor
      exact (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp hr'
    exact measurableSet_le (measurable_id.sub hr).abs measurable_const
  have hTpos : ∀ q ∈ Finset.Icc 1 ⌊R⌋₊, 0 < T q := by
    intro q hq
    have hq1 : 0 < q := by have := (Finset.mem_Icc.mp hq).1; omega
    have hqp : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
    dsimp [T, R]
    positivity
  obtain ⟨M, hM⟩ := hϕ.compact.exists_bound_of_continuous hϕ.smooth.continuous
  have hMb : ∀ x, |ϕ x| ≤ max M 0 := by
    intro x
    exact (show |ϕ x| ≤ M by simpa only [Real.norm_eq_abs] using hM x).trans (le_max_left _ _)
  have hS : MemLp (fun α => Sphi ϕ N α ^ 2) 2 (volume.restrict (Set.Ioc 0 1)) := by
    simpa [arcSquare328] using
      (arcSquare_memLp328 (ϕ := ϕ) (V := fun _ => (1 : ℂ)) continuous_const
        (s := Set.univ) MeasurableSet.univ N)
  have hb1 : MemLp (fun α => Sphi ϕ N α ^ 2 * (1 - bRhat G R T α)) 2
      (volume.restrict (Set.Ioc 0 1)) := by
    simpa [arcSquare328] using
      (arcSquare_memLp328 ϕ (continuous_error_multiplier328 hG hX ϑ hη)
        (s := Set.univ) MeasurableSet.univ N)
  have hbR : MemLp (fun α => Sphi ϕ N α ^ 2 * bRhat G R T α) 2
      (volume.restrict (Set.Ioc 0 1)) := by
    have h := hS.sub hb1
    have heq : (fun α => Sphi ϕ N α ^ 2 * bRhat G R T α) =
        ((fun α => Sphi ϕ N α ^ 2) - fun α => Sphi ϕ N α ^ 2 * (1 - bRhat G R T α)) := by
      funext α
      show Sphi ϕ N α ^ 2 * bRhat G R T α = Sphi ϕ N α ^ 2 - Sphi ϕ N α ^ 2 * (1 - bRhat G R T α)
      ring
    rw [heq]
    exact h
  obtain ⟨Cc, hCc0, hCc⟩ := continuousModel_bound405 hG R T
  have hcM : MemLp (fun α => Sphi ϕ N α ^ 2 * continuousModel405 G R T α) 2
      (volume.restrict (Set.Ioc 0 1)) :=
    smoothed_multiplier_memLp261 (le_max_right M 0) hMb
      (measurable_continuousModel405 hG R T) hCc0 hCc N
  have hnear := nearSquare_memLp328 ϕ hG.supp hXp hRp hη N
  have hMem1 : MemLp (fun α => Sphi ϕ N α ^ 2 *
      (nearTransform328 G X R η α - bRhat G R T α)) 2 (volume.restrict (Set.Ioc 0 1)) := by
    have h := hnear.sub hbR
    have heq : (fun α => Sphi ϕ N α ^ 2 * (nearTransform328 G X R η α - bRhat G R T α)) =
        ((fun α => Sphi ϕ N α ^ 2 * nearTransform328 G X R η α) -
          fun α => Sphi ϕ N α ^ 2 * bRhat G R T α) := by
      funext α
      show Sphi ϕ N α ^ 2 * (nearTransform328 G X R η α - bRhat G R T α) = Sphi ϕ N α ^ 2 * nearTransform328 G X R η α - Sphi ϕ N α ^ 2 * bRhat G R T α
      ring
    rw [heq]
    exact h
  have hMem2 : MemLp (fun α => Sphi ϕ N α ^ 2 *
      (continuousModel405 G R T α - bRhat G R T α)) 2 (volume.restrict (Set.Ioc 0 1)) := by
    have h := hcM.sub hbR
    have heq : (fun α => Sphi ϕ N α ^ 2 * (continuousModel405 G R T α - bRhat G R T α)) =
        ((fun α => Sphi ϕ N α ^ 2 * continuousModel405 G R T α) -
          fun α => Sphi ϕ N α ^ 2 * bRhat G R T α) := by
      funext α
      show Sphi ϕ N α ^ 2 * (continuousModel405 G R T α - bRhat G R T α) = Sphi ϕ N α ^ 2 * continuousModel405 G R T α - Sphi ϕ N α ^ 2 * bRhat G R T α
      ring
    rw [heq]
    exact h
  have hMemFull : MemLp (fun α => Sphi ϕ N α ^ 2 *
      (nearTransform328 G X R η α - continuousModel405 G R T α)) 2
      (volume.restrict (Set.Ioc 0 1)) := by
    have h := hnear.sub hcM
    have heq : (fun α => Sphi ϕ N α ^ 2 *
          (nearTransform328 G X R η α - continuousModel405 G R T α)) =
        ((fun α => Sphi ϕ N α ^ 2 * nearTransform328 G X R η α) -
          fun α => Sphi ϕ N α ^ 2 * continuousModel405 G R T α) := by
      funext α
      show Sphi ϕ N α ^ 2 * (nearTransform328 G X R η α - continuousModel405 G R T α) = Sphi ϕ N α ^ 2 * nearTransform328 G X R η α - Sphi ϕ N α ^ 2 * continuousModel405 G R T α
      ring
    rw [heq]
    exact h
  have hi1 := masked_intervalIntegrable405 hA hMem1
  have hi2 := masked_intervalIntegrable405 hA hMem2
  have hfull : continuousTail405 ϕ G X N ϑ η = ∫ α in (0 : ℝ)..1, A.indicator g α := by
    have htail := majorTail_eq_integral328 (ϕ := ϕ) hG hX N ϑ (η := η) hη
    have halias : aliasCoefficient405 ϕ G X N ϑ η = ∫ α in (0 : ℝ)..1,
        A.indicator (fun α => Sphi ϕ N α ^ 2 *
          (continuousModel405 G R T α - bRhat G R T α) * ee (-(N * α))) α := rfl
    rw [continuousTail405, htail, halias, ← intervalIntegral.integral_sub hi1 hi2]
    apply intervalIntegral.integral_congr
    intro α hα
    by_cases ha : α ∈ A
    · simp only [Set.indicator_of_mem ha]
      simp only [g]
      ring
    · simp only [Set.indicator_of_notMem ha, mul_zero, sub_zero]
  have hiA : IntervalIntegrable (fun α => A.indicator g α) volume 0 1 :=
    masked_intervalIntegrable405 hA hMemFull
  have hiLeft : IntervalIntegrable (fun α => (A ∩ I).indicator g α) volume 0 1 := by
    have h1 : (fun α => (A ∩ I).indicator g α) =
        (fun α => (A ∩ I).indicator (A.indicator g) α) := by
      funext α
      by_cases hα : α ∈ A ∩ I
      · rw [Set.indicator_of_mem hα, Set.indicator_of_mem hα, Set.indicator_of_mem hα.1]
      · rw [Set.indicator_of_notMem hα, Set.indicator_of_notMem hα]
    rw [h1]
    exact ⟨hiA.1.indicator (hA.inter hI), hiA.2.indicator (hA.inter hI)⟩
  have hiRight : IntervalIntegrable (fun α => (A ∩ Iᶜ).indicator g α) volume 0 1 := by
    have h1 : (fun α => (A ∩ Iᶜ).indicator g α) =
        (fun α => (A ∩ Iᶜ).indicator (A.indicator g) α) := by
      funext α
      by_cases hα : α ∈ A ∩ Iᶜ
      · rw [Set.indicator_of_mem hα, Set.indicator_of_mem hα, Set.indicator_of_mem hα.1]
      · rw [Set.indicator_of_notMem hα, Set.indicator_of_notMem hα]
    rw [h1]
    exact ⟨hiA.1.indicator (hA.diff hI), hiA.2.indicator (hA.diff hI)⟩
  have hpt : (fun α => (A ∩ I).indicator g α + (A ∩ Iᶜ).indicator g α) = A.indicator g := by
    funext α
    by_cases ha : α ∈ A
    · by_cases hi : α ∈ I
      · have h1 : α ∈ A ∩ I := ⟨ha, hi⟩
        have h2 : α ∉ A ∩ Iᶜ := fun h => h.2 hi
        rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, Set.indicator_of_mem ha,
          add_zero]
      · have h1 : α ∉ A ∩ I := fun h => hi h.2
        have h2 : α ∈ A ∩ Iᶜ := ⟨ha, hi⟩
        rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2, Set.indicator_of_mem ha,
          zero_add]
    · have h1 : α ∉ A ∩ I := fun h => ha h.1
      have h2 : α ∉ A ∩ Iᶜ := fun h => ha h.1
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, Set.indicator_of_notMem ha,
        add_zero]
  rw [hfull, ← hpt, intervalIntegral.integral_add hiLeft hiRight]


/-- LEAF. Step 2, the denominator one region: on the major arcs whose centre is an
integer the mean square over the smoothing family of the continuous tail coefficient is
of order eta to the fourth times X cubed times the fifth power of the logarithm. Only the
region near the integers enters, so the rational pair count of the remaining arcs is not
incurred here. -/
theorem leaf_denominator_one405 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1,
          ({α : ℝ | MajorArc X ((X : ℝ) ^ ϑ) α} ∩
            {α : ℝ | |α - ((round α : ℤ) : ℝ)| ≤ (X : ℝ) ^ ϑ / (X : ℝ)}).indicator
            (fun α => Sphi ϕ N α ^ 2 *
              (nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
                continuousModel405 G ((X : ℝ) ^ ϑ)
                  (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))) α‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  classical
  obtain ⟨M, hM⟩ := hϕ.compact.exists_bound_of_continuous hϕ.smooth.continuous
  have hMb : ∀ x, |ϕ x| ≤ max M 0 := by
    intro x
    exact (show |ϕ x| ≤ M by simpa only [Real.norm_eq_abs] using hM x).trans (le_max_left _ _)
  obtain ⟨Cf, hCf, hf⟩ := smoothed_family_bound261 hϕ
  obtain ⟨B, hB0, hB⟩ := near_model_den_one_bound405 hG ϑ hϑ
  refine ⟨16 * (Cf * B ^ 2), by positivity, ?_⟩
  intro X hX η hη hη1 hscale
  let R : ℝ := (X : ℝ) ^ ϑ
  let T : ℕ → ℝ := fun q => η * X * q / R
  let s : Set ℝ := {α : ℝ | MajorArc X R α} ∩
    {α : ℝ | |α - ((round α : ℤ) : ℝ)| ≤ R / (X : ℝ)}
  let W : ℝ → ℂ := fun α => if α ∈ Set.Icc (0 : ℝ) 1 then
    s.indicator (fun α => nearTransform328 G X R η α - continuousModel405 G R T α) α else 0
  have hXp : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hRp : 0 < R := Real.rpow_pos_of_pos hXp ϑ
  have hI : MeasurableSet {α : ℝ | |α - ((round α : ℤ) : ℝ)| ≤ R / (X : ℝ)} := by
    have hr : Measurable (fun β : ℝ => ((round β : ℤ) : ℝ)) := by
      have hr' : Measurable (fun β : ℝ => round β) := by
        simp_rw [round_eq]
        exact (measurable_id.add_const (1 / 2 : ℝ)).floor
      exact (measurable_of_countable (fun n : ℤ => (n : ℝ))).comp hr'
    exact measurableSet_le (measurable_id.sub hr).abs measurable_const
  have hs : MeasurableSet s := (measurableSet_majorArc84 X R).inter hI
  have hcM : Measurable (fun α => nearTransform328 G X R η α - continuousModel405 G R T α) :=
    (measurable_nearTransform328 hG.supp hXp hRp hη).sub
      (measurable_continuousModel405 hG R T)
  have hW : Measurable W := by
    unfold W
    exact (hcM.indicator hs).ite measurableSet_Icc measurable_const
  have hWB : ∀ α, ‖W α‖ ≤ B * η ^ 2 := by
    intro α
    by_cases h1 : α ∈ Set.Icc (0 : ℝ) 1
    · rw [show W α = s.indicator (fun α => nearTransform328 G X R η α -
        continuousModel405 G R T α) α from if_pos h1]
      by_cases h2 : α ∈ s
      · rw [Set.indicator_of_mem h2]
        exact hB X hX η hη hη1 hscale α h1 h2.2 h2.1
      · rw [Set.indicator_of_notMem h2, norm_zero]
        positivity
    · rw [show W α = 0 from if_neg h1, norm_zero]
      positivity
  have hfam := hf X hX W hW (B * η ^ 2) (by positivity) hWB
  have heq : ∀ N : ℕ, (∫ α in (0 : ℝ)..1,
        ({α : ℝ | MajorArc X R α} ∩
          {α : ℝ | |α - ((round α : ℤ) : ℝ)| ≤ R / (X : ℝ)}).indicator
          (fun α => Sphi ϕ N α ^ 2 *
            (nearTransform328 G X R η α - continuousModel405 G R T α) * ee (-(N * α))) α) =
      ∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * W α * ee (-(N * α)) := by
    intro N
    apply intervalIntegral.integral_congr
    intro α hα
    dsimp only
    have hα' : α ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hα
    by_cases h2 : α ∈ s
    · have hWα : W α = nearTransform328 G X R η α - continuousModel405 G R T α := by
        rw [show W α = s.indicator (fun α => nearTransform328 G X R η α -
          continuousModel405 G R T α) α from if_pos hα']
        exact Set.indicator_of_mem h2 _
      rw [Set.indicator_of_mem h2, hWα]
    · have hWα : W α = 0 := by
        rw [show W α = s.indicator (fun α => nearTransform328 G X R η α -
          continuousModel405 G R T α) α from if_pos hα']
        exact Set.indicator_of_notMem h2 _
      rw [Set.indicator_of_notMem h2, hWα]
      ring
  have hsum_eq : ∀ N : ℕ, ‖∫ α in (0 : ℝ)..1,
        ({α : ℝ | MajorArc X R α} ∩
          {α : ℝ | |α - ((round α : ℤ) : ℝ)| ≤ R / (X : ℝ)}).indicator
          (fun α => Sphi ϕ N α ^ 2 *
            (nearTransform328 G X R η α - continuousModel405 G R T α) * ee (-(N * α))) α‖ ^ 2 =
      ‖∫ α in (0 : ℝ)..1, Sphi ϕ N α ^ 2 * W α * ee (-(N * α))‖ ^ 2 := by
    intro N
    rw [heq N]
  rw [Finset.sum_congr rfl (fun N _ => hsum_eq N)]
  have hmain : Cf * (B * η ^ 2) ^ 2 * (X : ℝ) ^ 3 * Real.log X =
      Cf * B ^ 2 * η ^ 4 * (X : ℝ) ^ 3 * Real.log X := by ring
  rw [hmain] at hfam
  have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_natCast_nonneg X
  have hhalf : (1 / 2 : ℝ) ≤ Real.log X := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ X by exact_mod_cast hX)
    linarith [Real.log_two_gt_d9]
  have hlog5 : Real.log (X : ℝ) ≤ 16 * Real.log X ^ 5 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hhalf 4
    have hh := mul_le_mul_of_nonneg_right hp hlog
    norm_num at hh
    nlinarith only [hh]
  have hstep := mul_le_mul_of_nonneg_left hlog5
    (by positivity : (0 : ℝ) ≤ Cf * B ^ 2 * η ^ 4 * (X : ℝ) ^ 3)
  have hgoal : Cf * B ^ 2 * η ^ 4 * (X : ℝ) ^ 3 * (16 * Real.log X ^ 5) =
      16 * (Cf * B ^ 2) * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by ring
  linarith [hfam, hstep, hgoal]


/-- LEAF. Step 3, the remaining major arcs: on the major arcs whose centre is not an
integer the same mean square over the smoothing family is of order eta to the fourth
times X cubed times the fifth power of the logarithm. This region carries the rational
centres of denominator at least two together with the full rational sum of the model, so
the pair count and the separation of distinct centres are needed here. -/
theorem leaf_other_arcs405 {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X,
        ‖∫ α in (0 : ℝ)..1,
          ({α : ℝ | MajorArc X ((X : ℝ) ^ ϑ) α} ∩
            {α : ℝ | |α - ((round α : ℤ) : ℝ)| ≤ (X : ℝ) ^ ϑ / (X : ℝ)}ᶜ).indicator
            (fun α => Sphi ϕ N α ^ 2 *
              (nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
                continuousModel405 G ((X : ℝ) ^ ϑ)
                  (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))) α‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  sorry

/-- The continuous tail family bound assembled from the three leaves above. -/
theorem continuous_tail_family405_split {ϕ G : ℝ → ℝ} (hϕ : IsPhi ϕ) (hG : IsMajorWeight G)
    (ϑ : ℝ) (hϑ : 0 < ϑ) (hϑ' : ϑ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℕ, 2 ≤ X → ∀ η : ℝ, 0 < η → η ≤ 1 →
      10 * ((X : ℝ) ^ ϑ) ^ 2 ≤ η * X →
      ∑ N ∈ Finset.Icc 1 X, ‖continuousTail405 ϕ G X N ϑ η‖ ^ 2 ≤
        C * η ^ 4 * (X : ℝ) ^ 3 * Real.log X ^ 5 := by
  obtain ⟨C₁, hC₁, h₁⟩ := leaf_denominator_one405 hϕ hG ϑ hϑ hϑ'
  obtain ⟨C₂, hC₂, h₂⟩ := leaf_other_arcs405 hϕ hG ϑ hϑ hϑ'
  refine ⟨2 * (C₁ + C₂), by positivity, ?_⟩
  intro X hX η hη hη1 hscale
  have hsplit := coefficient_split328 (Finset.Icc 1 X)
    (fun N => continuousTail405 ϕ G X N ϑ η)
    (fun N => ∫ α in (0 : ℝ)..1,
      ({α : ℝ | MajorArc X ((X : ℝ) ^ ϑ) α} ∩
        {α : ℝ | |α - ((round α : ℤ) : ℝ)| ≤ (X : ℝ) ^ ϑ / (X : ℝ)}).indicator
        (fun α => Sphi ϕ N α ^ 2 *
          (nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
            continuousModel405 G ((X : ℝ) ^ ϑ)
              (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))) α)
  have hsub : ∀ N ∈ Finset.Icc 1 X,
      ‖continuousTail405 ϕ G X N ϑ η -
        (∫ α in (0 : ℝ)..1,
          ({α : ℝ | MajorArc X ((X : ℝ) ^ ϑ) α} ∩
            {α : ℝ | |α - ((round α : ℤ) : ℝ)| ≤ (X : ℝ) ^ ϑ / (X : ℝ)}).indicator
            (fun α => Sphi ϕ N α ^ 2 *
              (nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
                continuousModel405 G ((X : ℝ) ^ ϑ)
                  (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))) α)‖ ^ 2 =
        ‖(∫ α in (0 : ℝ)..1,
          ({α : ℝ | MajorArc X ((X : ℝ) ^ ϑ) α} ∩
            {α : ℝ | |α - ((round α : ℤ) : ℝ)| ≤ (X : ℝ) ^ ϑ / (X : ℝ)}ᶜ).indicator
            (fun α => Sphi ϕ N α ^ 2 *
              (nearTransform328 G X ((X : ℝ) ^ ϑ) η α -
                continuousModel405 G ((X : ℝ) ^ ϑ)
                  (fun q => η * X * q / (X : ℝ) ^ ϑ) α) * ee (-(N * α))) α)‖ ^ 2 := by
    intro N _
    rw [leaf_region_split405 hϕ hG hX N ϑ hϑ hη]
    rw [add_sub_cancel_left]
  rw [Finset.sum_congr rfl hsub] at hsplit
  have hb₁ := h₁ X hX η hη hη1 hscale
  have hb₂ := h₂ X hX η hη hη1 hscale
  nlinarith only [hsplit, hb₁, hb₂]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.leaf_region_split405
#print axioms LeanLab.BhowmikGrimmelt2026.leaf_denominator_one405
#print axioms LeanLab.BhowmikGrimmelt2026.leaf_other_arcs405
#print axioms LeanLab.BhowmikGrimmelt2026.continuous_tail_family405_split
