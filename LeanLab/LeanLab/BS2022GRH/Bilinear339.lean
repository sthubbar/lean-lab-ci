/- AI wrote this Lean code for CODEX task339. Goldbach is open.
Finite rectangular identification in the proof of Theorem 7.
Journal pp. 1239 and 1240, display 32.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.SliceRemainder236
import LeanLab.BS2022GRH.SliceRanges236

namespace LeanLab.BS2022GRH.Bilinear339
open Real Finset Classical ChenThresholdGRH DecompC164c
noncomputable section

/-- Ordered large prime pairs in the relaxed rectangle on p. 1239.
The equal prime case is retained from the sealed triple slice. -/
def pairSet (n j : ℕ) (ε₁ : ℝ) : Finset (ℕ × ℕ) :=
  let K := ⌈(1 + ε₁) * n⌉₊ + 1
  (range K ×ˢ range K).filter (fun q =>
    q.1.Prime ∧ q.2.Prime ∧ U7153.yy n ≤ q.1 ∧ q.1 ≤ q.2 ∧
      Nat.Coprime (q.1 * q.2) n ∧ w n ε₁ j * q.1 * q.2 < n)

/-- The product axis of the bilinear rectangle, journal p. 1239. -/
def productSet (n j : ℕ) (ε₁ : ℝ) : Finset ℕ :=
  (pairSet n j ε₁).image (fun q => q.1 * q.2)

/-- The characteristic coefficient of ordered semiprime products on p. 1239. -/
def coefficient (n j : ℕ) (ε₁ : ℝ) (m : ℕ) : ℂ :=
  if m ∈ productSet n j ε₁ then 1 else 0

/-- The finite coefficient has the unit norm bound required by Lemma 8, p. 1222. -/
theorem coefficient_norm (n j m : ℕ) (ε₁ : ℝ) : ‖coefficient n j ε₁ m‖ ≤ 1 := by
  unfold coefficient
  split_ifs <;> simp

/-- Unique sorted prime factorization makes the product coefficient characteristic.
Finite identification on p. 1239 before display 32. -/
theorem pair_product_injective (n j : ℕ) (ε₁ : ℝ) :
    Set.InjOn (fun q : ℕ × ℕ => q.1 * q.2) (pairSet n j ε₁) := by
  intro q hq r hr heq
  obtain ⟨_, hq1, hq2, _, hqle, _⟩ := mem_filter.mp hq
  obtain ⟨_, hr1, hr2, _, hrle, _⟩ := mem_filter.mp hr
  have hp : [q.1, q.2].Perm [r.1, r.2] := perm_of_prod_eq_prod
    (by simpa using heq)
    (by intro p hp; simp at hp
        rcases hp with rfl | rfl; exact hq1.prime; exact hq2.prime)
    (by intro p hp; simp at hp
        rcases hp with rfl | rfl; exact hr1.prime; exact hr2.prime)
  have he : [q.1, q.2] = [r.1, r.2] :=
    List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (by simpa using hqle)
      (by simpa using hrle) hp
  have hh : q.1 = r.1 ∧ q.2 = r.2 := by simpa using he
  exact Prod.ext hh.1 hh.2

/-- Each product lies on the positive integer axis below N over w, p. 1239. -/
theorem product_mem_nRange {n j m : ℕ} {ε₁ : ℝ} (hn : 0 < n) (hε : 0 < ε₁)
    (hm : m ∈ productSet n j ε₁) : m ∈ Decomp148a.nRange ((n : ℝ) / w n ε₁ j) := by
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hm
  obtain ⟨_, hq1, hq2, _, _, _, hlt⟩ := mem_filter.mp hq
  have hprod : (q.1 * q.2 : ℝ) < (n : ℝ) / w n ε₁ j := by
    apply (lt_div_iff₀ (w_pos n j ε₁ hn hε)).mpr
    push_cast
    nlinarith
  simp only [Decomp148a.nRange, mem_Ico, Nat.lt_ceil]
  exact ⟨Nat.mul_pos hq1.pos hq2.pos, by simpa only [Nat.cast_mul] using hprod⟩

/-- The short prime axis has exactly the three slice endpoint guards, p. 1239. -/
theorem mem_prime_axis (n j p : ℕ) (ε₁ : ℝ) :
    p ∈ Decomp148a.pRange (min (U7153.yy n) ((1 + ε₁) * w n ε₁ j)) (w n ε₁ j) ↔
      p.Prime ∧ w n ε₁ j ≤ (p : ℝ) ∧ (p : ℝ) < U7153.yy n ∧
        (p : ℝ) < w n ε₁ j * (1 + ε₁) := by
  simp only [Decomp148a.pRange, mem_filter, mem_range, Nat.lt_ceil, lt_min_iff]
  rw [mul_comm (1 + ε₁)]
  tauto

/-- Prime axis elements respect the artificial finite box of the sealed slice.
This box contributes no extra endpoint loss, journal p. 1239. -/
theorem prime_axis_box {n j p : ℕ} {ε₁ : ℝ} (hn : 1 ≤ n) (hε : 0 < ε₁)
    (hp : p ∈ Decomp148a.pRange (min (U7153.yy n) ((1 + ε₁) * w n ε₁ j)) (w n ε₁ j)) :
    p ∈ range (⌈(1 + ε₁) * n⌉₊ + 1) := by
  have hpY := (mem_prime_axis n j p ε₁).mp hp
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hy : U7153.yy n ≤ (n : ℝ) := by
    unfold U7153.yy
    exact rpow_le_self_of_one_le hnR (by norm_num)
  have hpn : (p : ℝ) < (1 + ε₁) * n :=
    hpY.2.2.1.trans_le (hy.trans (le_mul_of_one_le_left (by positivity) (by linarith)))
  exact mem_range.mpr (Nat.lt_succ_of_le (Nat.lt_ceil.mpr hpn).le)

/-- The relaxed slice is an exact rectangle before congruence is imposed.
This is the finite independence step on journal p. 1239. -/
theorem mem_slice_rectangle {n j p q r : ℕ} {ε₁ : ℝ}
    (hn : 0 < n) (hε : 0 < ε₁) :
    ((p, q), r) ∈ slice n ε₁ j ↔
      (q, r) ∈ pairSet n j ε₁ ∧
        p ∈ Decomp148a.pRange (min (U7153.yy n) ((1 + ε₁) * w n ε₁ j)) (w n ε₁ j) := by
  have hzw : U7153.zz n ≤ w n ε₁ j := by
    unfold w
    exact le_mul_of_one_le_right (rpow_nonneg (by positivity) _)
      (one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + ε₁))
  constructor
  · intro ht
    obtain ⟨hbox, hp, hq, hr, hz, hpy, hyq, hqr, hcop, hlt, hwp, hpw⟩ := mem_filter.mp ht
    refine ⟨mem_filter.mpr ⟨?_, hq, hr, hyq, hqr, hcop, hlt⟩,
      (mem_prime_axis n j p ε₁).mpr ⟨hp, hwp, hpy, hpw⟩⟩
    exact mem_product.mpr ⟨(mem_product.mp (mem_product.mp hbox).1).2,
      (mem_product.mp hbox).2⟩
  · rintro ⟨hq, hp⟩
    have hpbox := prime_axis_box (Nat.one_le_iff_ne_zero.mpr hn.ne') hε hp
    obtain ⟨hqbox, hqprime, hrprime, hyq, hqr, hcop, hlt⟩ := mem_filter.mp hq
    obtain ⟨hpprime, hwp, hpy, hpw⟩ := (mem_prime_axis n j p ε₁).mp hp
    exact mem_filter.mpr ⟨mem_product.mpr
      ⟨mem_product.mpr ⟨hpbox, (mem_product.mp hqbox).1⟩, (mem_product.mp hqbox).2⟩,
      hpprime, hqprime, hrprime, hzw.trans hwp, hpy, hyq, hqr, hcop, hlt, hwp, hpw⟩

/-- Reindex a finite triple sum by the independent product and prime axes.
The injective ordered factorization preserves multiplicity, journal p. 1239. -/
theorem sum_slice_rectangle (n j : ℕ) (ε₁ : ℝ) (hn : 0 < n) (hε : 0 < ε₁)
    (f : ℕ → ℕ → ℂ) :
    (∑ t ∈ slice n ε₁ j, f (t.1.2 * t.2) t.1.1) =
      ∑ m ∈ productSet n j ε₁,
        ∑ p ∈ Decomp148a.pRange
          (min (U7153.yy n) ((1 + ε₁) * w n ε₁ j)) (w n ε₁ j), f m p := by
  rw [← sum_product']
  apply sum_bij (fun t _ => (t.1.2 * t.2, t.1.1))
  · intro t ht
    have ht' := (mem_slice_rectangle hn hε).mp ht
    exact mem_product.mpr ⟨mem_image_of_mem _ ht'.1, ht'.2⟩
  · intro t ht u hu he
    exact SliceRemainder236.slice_pair_product_injective ht hu
      (congrArg Prod.snd he) (congrArg Prod.fst he)
  · intro b hb
    obtain ⟨hm, hp⟩ := mem_product.mp hb
    obtain ⟨q, hq, heq⟩ := mem_image.mp hm
    refine ⟨((b.2, q.1), q.2), (mem_slice_rectangle hn hε).mpr ⟨hq, hp⟩, ?_⟩
    exact Prod.ext heq rfl
  · intro t ht
    rfl

/-- Extend the exact rectangle to the Lemma 8 integer range using its coefficient.
This introduces no integers outside the semiprime product image, p. 1239. -/
theorem sum_slice_coefficient (n j : ℕ) (ε₁ : ℝ) (hn : 0 < n) (hε : 0 < ε₁)
    (f : ℕ → ℕ → ℂ) :
    (∑ t ∈ slice n ε₁ j, f (t.1.2 * t.2) t.1.1) =
      ∑ m ∈ Decomp148a.nRange ((n : ℝ) / w n ε₁ j),
        ∑ p ∈ Decomp148a.pRange
          (min (U7153.yy n) ((1 + ε₁) * w n ε₁ j)) (w n ε₁ j),
            coefficient n j ε₁ m * f m p := by
  rw [sum_slice_rectangle n j ε₁ hn hε]
  calc
    _ = ∑ m ∈ productSet n j ε₁,
        ∑ p ∈ Decomp148a.pRange
          (min (U7153.yy n) ((1 + ε₁) * w n ε₁ j)) (w n ε₁ j),
            coefficient n j ε₁ m * f m p := by
      apply sum_congr rfl
      intro m hm
      simp [coefficient, hm]
    _ = _ := sum_subset (fun m hm => product_mem_nRange hn hε hm)
      (by intro m hm hnot; simp [coefficient, hnot])

/-- A filtered triple cardinality equals the corresponding bilinear weighted count.
Both congruence and coprimality predicates fit this identity, journal p. 1239. -/
theorem filtered_card_coefficient (n j : ℕ) (ε₁ : ℝ) (hn : 0 < n) (hε : 0 < ε₁)
    (R : ℕ → Prop) [DecidablePred R] :
    (((slice n ε₁ j).filter (fun t => R (t.1.1 * t.1.2 * t.2))).card : ℂ) =
      ∑ m ∈ Decomp148a.nRange ((n : ℝ) / w n ε₁ j),
        ∑ p ∈ (Decomp148a.pRange
          (min (U7153.yy n) ((1 + ε₁) * w n ε₁ j)) (w n ε₁ j)).filter
          (fun p => R (m * p)), coefficient n j ε₁ m := by
  have h := sum_slice_coefficient n j ε₁ hn hε
    (fun m p => if R (m * p) then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero, ← sum_filter] at h
  have he (t : (ℕ × ℕ) × ℕ) : (t.1.2 * t.2) * t.1.1 = t.1.1 * t.1.2 * t.2 := by ring
  simp only [he] at h
  simpa only [sum_const, nsmul_eq_mul, mul_one] using h

/-- The reduced real slice residue is exactly the complex bilinear discrepancy.
The totient denominator is d as in display 32 on p. 1240. -/
theorem discrepancy_eq_reduced (n j d : ℕ) (ε₁ : ℝ) (hn : 0 < n) (hε : 0 < ε₁) :
    Decomp148a.discrepancy (coefficient n j ε₁) ((n : ℝ) / w n ε₁ j)
      (min (U7153.yy n) ((1 + ε₁) * w n ε₁ j)) (w n ε₁ j) d n =
        (SliceRemainder236.reducedResidue n j d ε₁ : ℂ) := by
  unfold Decomp148a.discrepancy
  rw [← filtered_card_coefficient n j ε₁ hn hε (fun k => k % d = n % d),
    ← filtered_card_coefficient n j ε₁ hn hε (fun k => Nat.Coprime k d)]
  unfold SliceRemainder236.reducedResidue
  push_cast
  ring

/-- The discrepancy at n is one of the reduced residue maxima when d is coprime to n.
This is a finite maximum comparison for display 32 on p. 1240. -/
theorem discrepancy_le_max (c : ℕ → ℂ) (X Y Z : ℝ) (n d : ℕ)
    (hd : 0 < d) (hcop : Nat.Coprime n d) :
    ‖Decomp148a.discrepancy c X Y Z d n‖ ≤ Decomp148a.maxDiscrepancy c X Y Z d := by
  have hb : n % d ∈ (range d).filter (fun b => Nat.Coprime b d) := by
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt n hd), by simpa using hcop⟩
  have h := Finset.le_sup
    (f := fun b => (⟨‖Decomp148a.discrepancy c X Y Z d b‖, norm_nonneg _⟩ : NNReal)) hb
  have he : Decomp148a.discrepancy c X Y Z d (n % d) =
      Decomp148a.discrepancy c X Y Z d n := by
    simp only [Decomp148a.discrepancy, Nat.mod_mod]
  change (⟨‖Decomp148a.discrepancy c X Y Z d n‖, norm_nonneg _⟩ : NNReal) ≤ _
  simpa only [he] using h

/-- The sifting divisor range is contained in the Lemma 8 modulus range, p. 1240. -/
theorem divisor_mem_moduli {n d : ℕ} {A : ℝ} (hd : d ∈ divisors n A) :
    d ∈ Decomp148a.moduli (√(n : ℝ) / log n ^ (A + 1)) (n : ℤ) := by
  obtain ⟨hsq, hcop, hd0, hdlt⟩ := SliceRemainder236.divisor_spec hd
  simp only [Decomp148a.moduli, mem_filter, mem_Ico, Nat.lt_ceil,
    Int.natAbs_natCast]
  exact ⟨⟨hd0, hdlt⟩, hsq, hcop.symm⟩

/-- The full finite bilinear identification bounds the reduced residue sum.
This completes the coefficient and rectangle step of display 32 on p. 1240. -/
theorem reduced_sum_le_bilinear (n j : ℕ) (A ε₁ : ℝ) (hn : 0 < n) (hε : 0 < ε₁) :
    (∑ d ∈ divisors n A, |SliceRemainder236.reducedResidue n j d ε₁|) ≤
      Decomp148a.bilinear (coefficient n j ε₁) ((n : ℝ) / w n ε₁ j)
        (min (U7153.yy n) ((1 + ε₁) * w n ε₁ j)) (w n ε₁ j)
        (√(n : ℝ) / log n ^ (A + 1)) (n : ℤ) := by
  unfold Decomp148a.bilinear
  apply (sum_le_sum (fun d hd => ?_)).trans
    (sum_le_sum_of_subset_of_nonneg (fun d hd => divisor_mem_moduli hd)
      (fun d _ _ => by unfold Decomp148a.maxDiscrepancy; exact NNReal.coe_nonneg _))
  have hs := SliceRemainder236.divisor_spec hd
  simpa only [discrepancy_eq_reduced n j d ε₁ hn hε, Complex.norm_real, Real.norm_eq_abs]
    using discrepancy_le_max (coefficient n j ε₁) ((n : ℝ) / w n ε₁ j)
      (min (U7153.yy n) ((1 + ε₁) * w n ε₁ j)) (w n ε₁ j) n d hs.2.2.1 hs.2.1.symm

end
end LeanLab.BS2022GRH.Bilinear339

#print axioms LeanLab.BS2022GRH.Bilinear339.coefficient_norm
#print axioms LeanLab.BS2022GRH.Bilinear339.pair_product_injective
#print axioms LeanLab.BS2022GRH.Bilinear339.product_mem_nRange
#print axioms LeanLab.BS2022GRH.Bilinear339.mem_prime_axis
#print axioms LeanLab.BS2022GRH.Bilinear339.prime_axis_box
#print axioms LeanLab.BS2022GRH.Bilinear339.mem_slice_rectangle
#print axioms LeanLab.BS2022GRH.Bilinear339.sum_slice_rectangle
#print axioms LeanLab.BS2022GRH.Bilinear339.sum_slice_coefficient
#print axioms LeanLab.BS2022GRH.Bilinear339.filtered_card_coefficient
#print axioms LeanLab.BS2022GRH.Bilinear339.discrepancy_eq_reduced
#print axioms LeanLab.BS2022GRH.Bilinear339.discrepancy_le_max
#print axioms LeanLab.BS2022GRH.Bilinear339.divisor_mem_moduli
#print axioms LeanLab.BS2022GRH.Bilinear339.reduced_sum_le_bilinear
