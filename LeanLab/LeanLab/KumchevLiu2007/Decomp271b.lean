/-
Diagonal and off diagonal leaves for Lemma 3.8, pages 14 and 15.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp271a

namespace LeanLab.KumchevLiu2007.Task271b

open Real Complex Task129 Task129b
open scoped BigOperators

/-- Page 14 display 51. The squared norm of a finite complex sum splits
into its diagonal and ordered off diagonal terms. -/
theorem norm_sum_sq_split {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 =
      (∑ i ∈ s, ‖f i‖ ^ 2) +
      ∑ i ∈ s, ∑ j ∈ s.erase i, (f i * (starRingEnd ℂ) (f j)).re := by
  classical
  have full : ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ∑ j ∈ s, (f i * (starRingEnd ℂ) (f j)).re := by
    rw [Complex.sq_norm]
    have h := congrArg Complex.re (Complex.mul_conj (∑ i ∈ s, f i))
    simp only [Complex.ofReal_re] at h
    rw [← h]
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
    rw [Finset.sum_comm]
  rw [full, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_erase_add _ _ hi]
  have h : (f i * (starRingEnd ℂ) (f i)).re = ‖f i‖ ^ 2 := by
    simpa only [Complex.ofReal_re, Complex.normSq_eq_norm_sq] using
      congrArg Complex.re (Complex.mul_conj (f i))
  rw [h, add_comm]

/-- The smooth indicator on page 4 display 11 is either zero or one. -/
theorem smoothWeight_norm_le_one (q : ℕ) (Q : ℝ) :
    ‖(smoothWeight q Q : ℂ)‖ ≤ 1 := by
  classical
  unfold smoothWeight
  split <;> simp

/-- The reciprocal square tail over a natural interval telescopes. -/
theorem sum_inv_sq_Ioc_le (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    (∑ q ∈ Finset.Ioc a b, (1 / (q : ℝ) ^ 2)) ≤
      1 / (a : ℝ) - 1 / (b : ℝ) := by
  induction b generalizing a with
  | zero =>
      omega
  | succ b ih =>
      rcases Nat.eq_or_lt_of_le hab with rfl | hlt
      · simp only [Finset.Ioc_eq_empty_of_le (Nat.le_refl _), Finset.sum_empty]
        norm_num
      · have hab' : a ≤ b := by omega
        have hnot : b + 1 ∉ Finset.Ioc a b := by
          simp only [Finset.mem_Ioc]
          omega
        have heq : insert (b + 1) (Finset.Ioc a b) = Finset.Ioc a (b + 1) := by
          simpa using Finset.insert_Ioc_right_eq_Ioc_succ hab'
        rw [← heq, Finset.sum_insert hnot]
        have hi := ih a ha hab'
        push_cast at hi ⊢
        have hterm : 1 / (b + 1 : ℝ) ^ 2 ≤ 1 / (b : ℝ) - 1 / (b + 1 : ℝ) := by
          have hb_nat : 1 ≤ b := by omega
          have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb_nat
          field_simp
          nlinarith
        calc
          1 / (b + 1 : ℝ) ^ 2 + (∑ q ∈ Finset.Ioc a b, (1 / (q : ℝ) ^ 2))
              ≤ 1 / (b + 1 : ℝ) ^ 2 + (1 / (a : ℝ) - 1 / (b : ℝ)) := by
                simpa only [add_comm] using
                  add_le_add_right hi (1 / (b + 1 : ℝ) ^ 2)
          _ ≤ (1 / (b : ℝ) - 1 / (b + 1 : ℝ)) + (1 / (a : ℝ) - 1 / (b : ℝ)) := by
                gcongr
          _ = 1 / (a : ℝ) - 1 / (b + 1 : ℝ) := by ring

private lemma ee_add_292a (s t : ℝ) : U1534.ee s * U1534.ee t = U1534.ee (s + t) := by
  unfold U1534.ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The classical Ramanujan-sum form: `∑_a gaussS q a · e(-a n/q)` is a double sum over
units `(x, a)` of `e(a (x² - n)/q)`. -/
private lemma A2_pair_form (n q : ℕ) (hq : 0 < q) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        U1534.gaussS q a * U1534.ee (-(((a * n : ℕ) : ℝ) / (q : ℝ))))
      = ∑ x ∈ (Finset.range q).filter (fun x => Nat.Coprime x q),
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            U1534.ee (((((a : ℤ) * ((x : ℤ) ^ 2 - (n : ℤ))) : ℤ) : ℝ) / (q : ℝ)) := by
  classical
  set S : Finset ℕ := (Finset.range q).filter (fun a => Nat.Coprime a q) with hS
  have hstep : ∀ a ∈ S,
      U1534.gaussS q a * U1534.ee (-(((a * n : ℕ) : ℝ) / (q : ℝ)))
        = ∑ x ∈ S, U1534.ee (((((a : ℤ) * ((x : ℤ) ^ 2 - (n : ℤ))) : ℤ) : ℝ) / (q : ℝ)) := by
    intro a ha
    unfold U1534.gaussS
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro x hx
    have harg : ((a * x ^ 2 : ℕ) : ℝ) / (q : ℝ) + (-(((a * n : ℕ) : ℝ) / (q : ℝ)))
        = ((((a : ℤ) * ((x : ℤ) ^ 2 - (n : ℤ))) : ℤ) : ℝ) / (q : ℝ) := by
      push_cast
      ring
    rw [← harg, ee_add_292a]
  calc (∑ a ∈ S, U1534.gaussS q a * U1534.ee (-(((a * n : ℕ) : ℝ) / (q : ℝ))))
      = ∑ a ∈ S, ∑ x ∈ S, U1534.ee (((((a : ℤ) * ((x : ℤ) ^ 2 - (n : ℤ))) : ℤ) : ℝ) / (q : ℝ)) :=
        Finset.sum_congr rfl hstep
    _ = ∑ x ∈ S, ∑ a ∈ S, U1534.ee (((((a : ℤ) * ((x : ℤ) ^ 2 - (n : ℤ))) : ℤ) : ℝ) / (q : ℝ)) :=
        Finset.sum_comm

/-- `ee` at a rational with denominator `q` is the standard additive character on `ZMod q`. -/
private lemma ee_eq_stdAddChar_292a (q : ℕ) [NeZero q] (j : ℤ) :
    U1534.ee ((j : ℝ) / (q : ℝ)) = ZMod.stdAddChar (N := q) (j : ZMod q) := by
  rw [ZMod.stdAddChar_coe]
  unfold U1534.ee
  congr 1
  push_cast
  ring

/-- Reindexing a sum over the unit residues of `q` as a sum over the units of `ZMod q`. -/
private lemma sum_units_eq_sum_zmod_units (q : ℕ) [NeZero q] (g : ℕ → ℂ) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), g a)
      = ∑ y ∈ (Finset.univ : Finset (ZMod q)).filter (fun y => IsUnit y), g y.val := by
  classical
  refine Finset.sum_bij (fun (a : ℕ) _ => (a : ZMod q)) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at ha ⊢
    rw [ZMod.isUnit_iff_coprime]
    exact ha.2
  · intro a1 ha1 a2 ha2 heq
    simp only [Finset.mem_filter, Finset.mem_range] at ha1 ha2
    have h := congrArg ZMod.val heq
    rwa [ZMod.val_natCast_of_lt ha1.1, ZMod.val_natCast_of_lt ha2.1] at h
  · intro y hy
    refine ⟨y.val, ?_, ZMod.natCast_zmod_val y⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt y, ?_⟩
    have hy' : IsUnit y := (Finset.mem_filter.mp hy).2
    rw [← ZMod.natCast_zmod_val y, ZMod.isUnit_iff_coprime] at hy'
    exact hy'
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    rw [ZMod.val_natCast_of_lt ha.1]

/-- The single-modulus character form of a unit sum. -/
private lemma ee_unit_char_292a (n q : ℕ) [NeZero q] :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        U1534.ee ((((a * n : ℕ) : ℝ) / (q : ℝ))))
      = ∑ y ∈ (Finset.univ : Finset (ZMod q)).filter (fun y => IsUnit y),
          ZMod.stdAddChar (N := q) ((n : ZMod q) * y) := by
  classical
  rw [sum_units_eq_sum_zmod_units q (fun a => U1534.ee ((((a * n : ℕ) : ℝ) / (q : ℝ))))]
  refine Finset.sum_congr rfl ?_
  intro y _
  have h := ee_eq_stdAddChar_292a q ((y.val : ℤ) * (n : ℤ))
  have hc : ((y.val * n : ℕ) : ℝ) = ((((y.val : ℤ) * (n : ℤ)) : ℤ) : ℝ) := by push_cast; ring
  rw [hc, h]
  congr 1
  push_cast
  rw [ZMod.natCast_zmod_val]
  ring


/-- The standard additive character splits across a coprime factorisation, with the
Bezout twist `gcdB` on the first factor and `gcdA` on the second. -/
private lemma stdAddChar_crt_split (q1 q2 : ℕ) [NeZero q1] [NeZero q2] [NeZero (q1 * q2)]
    (hcop : q1.Coprime q2) (k : ℤ) :
    ZMod.stdAddChar (N := q1 * q2) (k : ZMod (q1 * q2))
      = ZMod.stdAddChar (N := q1) ((k : ZMod q1) * ((Nat.gcdB q1 q2 : ℤ) : ZMod q1))
        * ZMod.stdAddChar (N := q2) ((k : ZMod q2) * ((Nat.gcdA q1 q2 : ℤ) : ZMod q2)) := by
  rw [ZMod.stdAddChar_coe]
  have hm1 : ((k : ZMod q1) * ((Nat.gcdB q1 q2 : ℤ) : ZMod q1))
      = (((k * Nat.gcdB q1 q2 : ℤ)) : ZMod q1) := by push_cast; ring
  have hm2 : ((k : ZMod q2) * ((Nat.gcdA q1 q2 : ℤ) : ZMod q2))
      = (((k * Nat.gcdA q1 q2 : ℤ)) : ZMod q2) := by push_cast; ring
  rw [hm1, hm2, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  have hbez : ((q1 : ℤ)) * Nat.gcdA q1 q2 + ((q2 : ℤ)) * Nat.gcdB q1 q2 = 1 := by
    have h := Nat.gcd_eq_gcd_ab q1 q2
    rw [hcop.gcd_eq_one] at h
    push_cast at h
    linarith
  have hbezC : ((q1 : ℕ) : ℂ) * ((Nat.gcdA q1 q2 : ℤ) : ℂ)
      + ((q2 : ℕ) : ℂ) * ((Nat.gcdB q1 q2 : ℤ) : ℂ) = 1 := by
    exact_mod_cast hbez
  have hq1n : (((q1 : ℕ)) : ℂ) ≠ 0 := by
    have h : 0 < q1 := NeZero.pos q1
    exact_mod_cast h.ne'
  have hq2n : (((q2 : ℕ)) : ℂ) ≠ 0 := by
    have h : 0 < q2 := NeZero.pos q2
    exact_mod_cast h.ne'
  push_cast
  field_simp
  linear_combination (-(↑k : ℂ)) * hbezC

/-- The CRT character splitting for an arbitrary residue class. -/
private lemma stdAddChar_crt_split' (q1 q2 : ℕ) [NeZero q1] [NeZero q2] [NeZero (q1 * q2)]
    (hcop : q1.Coprime q2) (w : ZMod (q1 * q2)) :
    ZMod.stdAddChar (N := q1 * q2) w
      = ZMod.stdAddChar (N := q1) ((ZMod.cast w : ZMod q1) * ((Nat.gcdB q1 q2 : ℤ) : ZMod q1))
        * ZMod.stdAddChar (N := q2) ((ZMod.cast w : ZMod q2) * ((Nat.gcdA q1 q2 : ℤ) : ZMod q2)) := by
  have hwz : (((w.val : ℤ)) : ZMod (q1 * q2)) = w := by
    rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val w
  rw [← hwz, stdAddChar_crt_split q1 q2 hcop (w.val : ℤ)]
  have e1 : (ZMod.cast (((w.val : ℤ)) : ZMod (q1 * q2)) : ZMod q1)
      = (((w.val : ℤ)) : ZMod q1) := by
    rw [show (((w.val : ℤ)) : ZMod (q1 * q2)) = ((w.val : ℕ) : ZMod (q1 * q2)) by rw [Int.cast_natCast]]
    rw [ZMod.cast_natCast (R := ZMod q1) (dvd_mul_right q1 q2) w.val]
    exact (Int.cast_natCast w.val).symm
  have e2 : (ZMod.cast (((w.val : ℤ)) : ZMod (q1 * q2)) : ZMod q2)
      = (((w.val : ℤ)) : ZMod q2) := by
    rw [show (((w.val : ℤ)) : ZMod (q1 * q2)) = ((w.val : ℕ) : ZMod (q1 * q2)) by rw [Int.cast_natCast]]
    rw [ZMod.cast_natCast (R := ZMod q2) (dvd_mul_left q2 q1) w.val]
    exact (Int.cast_natCast w.val).symm
  rw [e1, e2]

/-- The pair form of the coefficient, as a double sum of `ZMod` characters. -/
private lemma pair_form_zmod (n q : ℕ) [NeZero q] :
    (∑ x ∈ (Finset.range q).filter (fun x => Nat.Coprime x q),
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          U1534.ee (((((a : ℤ) * ((x : ℤ) ^ 2 - (n : ℤ))) : ℤ) : ℝ) / (q : ℝ)))
      = ∑ y ∈ (Finset.univ : Finset (ZMod q)).filter (fun y => IsUnit y),
          ∑ z ∈ (Finset.univ : Finset (ZMod q)).filter (fun z => IsUnit z),
            ZMod.stdAddChar (N := q) (z * (y * y - (n : ZMod q))) := by
  classical
  rw [sum_units_eq_sum_zmod_units q
    (fun x => ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      U1534.ee (((((a : ℤ) * ((x : ℤ) ^ 2 - (n : ℤ))) : ℤ) : ℝ) / (q : ℝ)))]
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [sum_units_eq_sum_zmod_units q
    (fun a => U1534.ee (((((a : ℤ) * ((y.val : ℤ) ^ 2 - (n : ℤ))) : ℤ) : ℝ) / (q : ℝ)))]
  refine Finset.sum_congr rfl ?_
  intro z _
  have h := ee_eq_stdAddChar_292a q (((z.val : ℤ) * ((y.val : ℤ) ^ 2 - (n : ℤ))))
  rw [h]
  congr 1
  push_cast
  rw [ZMod.natCast_zmod_val z, ZMod.natCast_zmod_val y]
  ring


/-- Multiplication by a unit permutes the unit residues. -/
private lemma sum_units_mul_shift (q : ℕ) [NeZero q] (u : ZMod q) (hu : IsUnit u)
    (G : ZMod q → ℂ) :
    (∑ z ∈ (Finset.univ : Finset (ZMod q)).filter (fun z => IsUnit z), G (z * u))
      = ∑ z ∈ (Finset.univ : Finset (ZMod q)).filter (fun z => IsUnit z), G z := by
  classical
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hvu : v * u = 1 := by rw [mul_comm]; exact hv
  have hvU : IsUnit v := isUnit_iff_exists.mpr ⟨u, hvu, hv⟩
  refine Finset.sum_bij (fun (z : ZMod q) _ => z * u) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact hz.mul hu
  · intro z1 hz1 z2 hz2 heq
    have h : z1 * u * v = z2 * u * v := by rw [heq]
    rwa [mul_assoc, mul_assoc, hv, mul_one, mul_one] at h
  · intro z hz
    refine ⟨z * v, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact hz.mul hvU
    · rw [mul_assoc, hvu, mul_one]
  · intro z hz
    rfl

/-- The Bezout coefficient `gcdB` is a unit modulo `q1` when `q1` and `q2` are coprime. -/
private lemma gcdB_isUnit (q1 q2 : ℕ) [NeZero q1] (hcop : q1.Coprime q2) :
    IsUnit (((Nat.gcdB q1 q2 : ℤ)) : ZMod q1) := by
  have hbez : ((q1 : ℤ)) * Nat.gcdA q1 q2 + ((q2 : ℤ)) * Nat.gcdB q1 q2 = 1 := by
    have h := Nat.gcd_eq_gcd_ab q1 q2
    rw [hcop.gcd_eq_one] at h
    push_cast at h
    linarith
  have h0 : (((q1 : ℤ)) : ZMod q1) = 0 := by push_cast; exact ZMod.natCast_self q1
  have hcast : ((q2 : ℤ) : ZMod q1) * ((Nat.gcdB q1 q2 : ℤ) : ZMod q1) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod q1)) hbez
    push_cast at h
    simpa [h0] using h
  exact isUnit_iff_exists.mpr ⟨((q2 : ℤ) : ZMod q1), by rwa [mul_comm], hcast⟩

/-- The Bezout coefficient `gcdA` is a unit modulo `q2` when `q1` and `q2` are coprime. -/
private lemma gcdA_isUnit (q1 q2 : ℕ) [NeZero q2] (hcop : q1.Coprime q2) :
    IsUnit (((Nat.gcdA q1 q2 : ℤ)) : ZMod q2) := by
  have hbez : ((q1 : ℤ)) * Nat.gcdA q1 q2 + ((q2 : ℤ)) * Nat.gcdB q1 q2 = 1 := by
    have h := Nat.gcd_eq_gcd_ab q1 q2
    rw [hcop.gcd_eq_one] at h
    push_cast at h
    linarith
  have h0 : (((q2 : ℤ)) : ZMod q2) = 0 := by push_cast; exact ZMod.natCast_self q2
  have hcast : ((q1 : ℤ) : ZMod q2) * ((Nat.gcdA q1 q2 : ℤ) : ZMod q2) = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod q2)) hbez
    push_cast at h
    simpa [h0] using h
  exact isUnit_iff_exists.mpr ⟨((q1 : ℤ) : ZMod q2), by rwa [mul_comm], hcast⟩

/-- Transporting a double unit-sum along the CRT equivalence. -/
private lemma sum_units_crt_transport (q1 q2 : ℕ) [NeZero q1] [NeZero q2] [NeZero (q1 * q2)]
    (hcop : q1.Coprime q2) (G : ZMod (q1 * q2) → ZMod (q1 * q2) → ℂ) :
    (∑ y ∈ (Finset.univ : Finset (ZMod (q1 * q2))).filter (fun y => IsUnit y),
        ∑ z ∈ (Finset.univ : Finset (ZMod (q1 * q2))).filter (fun z => IsUnit z), G y z)
      = ∑ p ∈ (Finset.univ : Finset (ZMod q1 × ZMod q2)).filter (fun p => IsUnit p),
          ∑ r ∈ (Finset.univ : Finset (ZMod q1 × ZMod q2)).filter (fun r => IsUnit r),
            G ((ZMod.chineseRemainder hcop).symm p) ((ZMod.chineseRemainder hcop).symm r) := by
  classical
  set e := ZMod.chineseRemainder hcop with he
  have hmem : ∀ p : ZMod q1 × ZMod q2, IsUnit p → IsUnit (e.symm p) := fun p hp =>
    IsUnit.map (e.symm : ZMod q1 × ZMod q2 →+* ZMod (q1 * q2)) hp
  have hmem' : ∀ p : ZMod (q1 * q2), IsUnit p → IsUnit (e p) := fun p hp =>
    IsUnit.map (e : ZMod (q1 * q2) →+* ZMod q1 × ZMod q2) hp
  have hinner : ∀ y : ZMod (q1 * q2),
      (∑ z ∈ (Finset.univ : Finset (ZMod (q1 * q2))).filter (fun z => IsUnit z), G y z)
        = ∑ r ∈ (Finset.univ : Finset (ZMod q1 × ZMod q2)).filter (fun r => IsUnit r),
            G y (e.symm r) := by
    intro y
    refine Finset.sum_bij (fun (z : ZMod (q1 * q2)) _ => e z) ?_ ?_ ?_ ?_
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact hmem' z hz
    · intro z1 hz1 z2 hz2 heq
      exact e.injective heq
    · intro r hr
      refine ⟨e.symm r, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      exact hmem r hr
    · intro z hz
      simp only [RingEquiv.symm_apply_apply]
  simp only [hinner]
  refine Finset.sum_bij (fun (y : ZMod (q1 * q2)) _ => e y) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hmem' y hy
  · intro y1 hy1 y2 hy2 heq
    exact e.injective heq
  · intro p hp
    refine ⟨e.symm p, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hmem p hp
  · intro y hy
    simp only [RingEquiv.symm_apply_apply]

/-- First component of the CRT inverse is the cast to `ZMod q1`. -/
private lemma cast_crt_symm_fst (q1 q2 : ℕ) [NeZero q1] [NeZero q2] [NeZero (q1 * q2)]
    (hcop : q1.Coprime q2) (p : ZMod q1 × ZMod q2) :
    (ZMod.cast ((ZMod.chineseRemainder hcop).symm p) : ZMod q1) = p.1 := by
  have h : ZMod.chineseRemainder hcop ((ZMod.chineseRemainder hcop).symm p) = p :=
    RingEquiv.apply_symm_apply _ _
  have h1 := congrArg Prod.fst h
  rw [← h1]
  simp [ZMod.chineseRemainder, ZMod.castHom_apply]

/-- Second component of the CRT inverse is the cast to `ZMod q2`. -/
private lemma cast_crt_symm_snd (q1 q2 : ℕ) [NeZero q1] [NeZero q2] [NeZero (q1 * q2)]
    (hcop : q1.Coprime q2) (p : ZMod q1 × ZMod q2) :
    (ZMod.cast ((ZMod.chineseRemainder hcop).symm p) : ZMod q2) = p.2 := by
  have h : ZMod.chineseRemainder hcop ((ZMod.chineseRemainder hcop).symm p) = p :=
    RingEquiv.apply_symm_apply _ _
  have h1 := congrArg Prod.snd h
  rw [← h1]
  simp [ZMod.chineseRemainder, ZMod.castHom_apply]


/-- A quadruple sum of outer products is the product of the two double sums. -/
private lemma quadruple_sum_mul {α β : Type*} (F1 : Finset α) (F2 : Finset β)
    (A : α → α → ℂ) (B : β → β → ℂ) :
    (∑ p1 ∈ F1, ∑ p2 ∈ F2, ∑ r1 ∈ F1, ∑ r2 ∈ F2, A p1 r1 * B p2 r2)
      = (∑ p1 ∈ F1, ∑ r1 ∈ F1, A p1 r1) * (∑ p2 ∈ F2, ∑ r2 ∈ F2, B p2 r2) := by
  rw [Finset.sum_mul_sum F1 F2 (fun p1 => ∑ r1 ∈ F1, A p1 r1)
    (fun p2 => ∑ r2 ∈ F2, B p2 r2)]
  refine Finset.sum_congr rfl ?_
  intro p1 _
  refine Finset.sum_congr rfl ?_
  intro p2 _
  rw [Finset.sum_mul_sum]

/-- The pointwise CRT factorisation of one summand, with the Bezout twist. -/
private lemma V_term_factor (n q1 q2 : ℕ) [NeZero q1] [NeZero q2] [NeZero (q1 * q2)]
    (hcop : q1.Coprime q2) (p1 : ZMod q1) (p2 : ZMod q2) (r1 : ZMod q1) (r2 : ZMod q2) :
    ZMod.stdAddChar (N := q1 * q2)
        ((ZMod.chineseRemainder hcop).symm (r1, r2)
          * ((ZMod.chineseRemainder hcop).symm (p1, p2)
              * (ZMod.chineseRemainder hcop).symm (p1, p2) - (n : ZMod (q1 * q2))))
      = ZMod.stdAddChar (N := q1)
          (((Nat.gcdB q1 q2 : ℤ) : ZMod q1) * (r1 * (p1 * p1 - (n : ZMod q1))))
        * ZMod.stdAddChar (N := q2)
          (((Nat.gcdA q1 q2 : ℤ) : ZMod q2) * (r2 * (p2 * p2 - (n : ZMod q2)))) := by
  have hd1 : q1 ∣ q1 * q2 := dvd_mul_right q1 q2
  have hd2 : q2 ∣ q1 * q2 := dvd_mul_left q2 q1
  have hn1 : (ZMod.cast ((n : ℕ) : ZMod (q1 * q2)) : ZMod q1) = ((n : ℕ) : ZMod q1) :=
    ZMod.cast_natCast (R := ZMod q1) hd1 n
  have hn2 : (ZMod.cast ((n : ℕ) : ZMod (q1 * q2)) : ZMod q2) = ((n : ℕ) : ZMod q2) :=
    ZMod.cast_natCast (R := ZMod q2) hd2 n
  have hcw1 : (ZMod.cast ((ZMod.chineseRemainder hcop).symm (r1, r2)
      * ((ZMod.chineseRemainder hcop).symm (p1, p2)
          * (ZMod.chineseRemainder hcop).symm (p1, p2) - (n : ZMod (q1 * q2)))) : ZMod q1)
      = r1 * (p1 * p1 - (n : ZMod q1)) := by
    rw [ZMod.cast_mul hd1, ZMod.cast_sub hd1, ZMod.cast_mul hd1, hn1]
    simp only [cast_crt_symm_fst, Prod.fst, Prod.snd]
  have hcw2 : (ZMod.cast ((ZMod.chineseRemainder hcop).symm (r1, r2)
      * ((ZMod.chineseRemainder hcop).symm (p1, p2)
          * (ZMod.chineseRemainder hcop).symm (p1, p2) - (n : ZMod (q1 * q2)))) : ZMod q2)
      = r2 * (p2 * p2 - (n : ZMod q2)) := by
    rw [ZMod.cast_mul hd2, ZMod.cast_sub hd2, ZMod.cast_mul hd2, hn2]
    simp only [cast_crt_symm_snd, Prod.fst, Prod.snd]
  rw [stdAddChar_crt_split' q1 q2 hcop
    ((ZMod.chineseRemainder hcop).symm (r1, r2)
      * ((ZMod.chineseRemainder hcop).symm (p1, p2)
          * (ZMod.chineseRemainder hcop).symm (p1, p2) - (n : ZMod (q1 * q2)))), hcw1, hcw2]
  rw [mul_comm (r1 * (p1 * p1 - (n : ZMod q1))) (((Nat.gcdB q1 q2 : ℤ) : ZMod q1)),
    mul_comm (r2 * (p2 * p2 - (n : ZMod q2))) (((Nat.gcdA q1 q2 : ℤ) : ZMod q2))]

/-- The multiplicative splitting of the unit double sum across a coprime factorisation. -/
private lemma V_coprime_mul (n q1 q2 : ℕ) [NeZero q1] [NeZero q2] [NeZero (q1 * q2)]
    (hcop : q1.Coprime q2) :
    (∑ y ∈ (Finset.univ : Finset (ZMod (q1 * q2))).filter (fun y => IsUnit y),
        ∑ z ∈ (Finset.univ : Finset (ZMod (q1 * q2))).filter (fun z => IsUnit z),
          ZMod.stdAddChar (N := q1 * q2) (z * (y * y - (n : ZMod (q1 * q2)))))
      = (∑ y ∈ (Finset.univ : Finset (ZMod q1)).filter (fun y => IsUnit y),
          ∑ z ∈ (Finset.univ : Finset (ZMod q1)).filter (fun z => IsUnit z),
            ZMod.stdAddChar (N := q1) (z * (y * y - (n : ZMod q1))))
        * (∑ y ∈ (Finset.univ : Finset (ZMod q2)).filter (fun y => IsUnit y),
          ∑ z ∈ (Finset.univ : Finset (ZMod q2)).filter (fun z => IsUnit z),
            ZMod.stdAddChar (N := q2) (z * (y * y - (n : ZMod q2)))) := by
  classical
  set F1 : Finset (ZMod q1) := Finset.univ.filter (fun a => IsUnit a) with hF1
  set F2 : Finset (ZMod q2) := Finset.univ.filter (fun a => IsUnit a) with hF2
  have hF' : (Finset.univ.filter (fun p : ZMod q1 × ZMod q2 => IsUnit p)) = F1 ×ˢ F2 := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, hF1, hF2]
    exact Prod.isUnit_iff
  -- strip the Bezout twist from each of the two right-hand factors
  have hkey1 : (∑ p1 ∈ F1, ∑ r1 ∈ F1,
        ZMod.stdAddChar (N := q1) (r1 * (p1 * p1 - (n : ZMod q1))))
      = ∑ p1 ∈ F1, ∑ r1 ∈ F1, ZMod.stdAddChar (N := q1)
          (((Nat.gcdB q1 q2 : ℤ) : ZMod q1) * (r1 * (p1 * p1 - (n : ZMod q1)))) := by
    refine Finset.sum_congr rfl (fun p1 _ => ?_)
    have h := sum_units_mul_shift q1 (((Nat.gcdB q1 q2 : ℤ) : ZMod q1))
      (gcdB_isUnit q1 q2 hcop)
      (fun z => ZMod.stdAddChar (N := q1) (z * (p1 * p1 - (n : ZMod q1))))
    rw [← h]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    congr 1
    ring
  have hkey2 : (∑ p2 ∈ F2, ∑ r2 ∈ F2,
        ZMod.stdAddChar (N := q2) (r2 * (p2 * p2 - (n : ZMod q2))))
      = ∑ p2 ∈ F2, ∑ r2 ∈ F2, ZMod.stdAddChar (N := q2)
          (((Nat.gcdA q1 q2 : ℤ) : ZMod q2) * (r2 * (p2 * p2 - (n : ZMod q2)))) := by
    refine Finset.sum_congr rfl (fun p2 _ => ?_)
    have h := sum_units_mul_shift q2 (((Nat.gcdA q1 q2 : ℤ) : ZMod q2))
      (gcdA_isUnit q1 q2 hcop)
      (fun z => ZMod.stdAddChar (N := q2) (z * (p2 * p2 - (n : ZMod q2))))
    rw [← h]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    congr 1
    ring
  rw [hkey1, hkey2]
  clear hkey1 hkey2
  rw [sum_units_crt_transport q1 q2 hcop
    (fun y z => ZMod.stdAddChar (N := q1 * q2) (z * (y * y - (n : ZMod (q1 * q2)))))]
  rw [hF']
  have hmix : (∑ p ∈ F1 ×ˢ F2, ∑ r ∈ F1 ×ˢ F2,
        ZMod.stdAddChar (N := q1 * q2)
          ((ZMod.chineseRemainder hcop).symm r
            * ((ZMod.chineseRemainder hcop).symm p
                * (ZMod.chineseRemainder hcop).symm p - (n : ZMod (q1 * q2)))))
      = ∑ p1 ∈ F1, ∑ p2 ∈ F2, ∑ r1 ∈ F1, ∑ r2 ∈ F2,
          ZMod.stdAddChar (N := q1 * q2)
            ((ZMod.chineseRemainder hcop).symm (r1, r2)
              * ((ZMod.chineseRemainder hcop).symm (p1, p2)
                  * (ZMod.chineseRemainder hcop).symm (p1, p2) - (n : ZMod (q1 * q2)))) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun p1 _ => Finset.sum_congr rfl (fun p2 _ => ?_))
    rw [Finset.sum_product]
  rw [hmix]
  clear hmix
  have hstep : (∑ p1 ∈ F1, ∑ p2 ∈ F2, ∑ r1 ∈ F1, ∑ r2 ∈ F2,
        ZMod.stdAddChar (N := q1 * q2)
          ((ZMod.chineseRemainder hcop).symm (r1, r2)
            * ((ZMod.chineseRemainder hcop).symm (p1, p2)
                * (ZMod.chineseRemainder hcop).symm (p1, p2) - (n : ZMod (q1 * q2)))))
      = ∑ p1 ∈ F1, ∑ p2 ∈ F2, ∑ r1 ∈ F1, ∑ r2 ∈ F2,
          ZMod.stdAddChar (N := q1)
              (((Nat.gcdB q1 q2 : ℤ) : ZMod q1) * (r1 * (p1 * p1 - (n : ZMod q1))))
            * ZMod.stdAddChar (N := q2)
              (((Nat.gcdA q1 q2 : ℤ) : ZMod q2) * (r2 * (p2 * p2 - (n : ZMod q2)))) := by
    refine Finset.sum_congr rfl (fun p1 _ => Finset.sum_congr rfl (fun p2 _ =>
      Finset.sum_congr rfl (fun r1 _ => Finset.sum_congr rfl (fun r2 _ => ?_))))
    exact V_term_factor n q1 q2 hcop p1 p2 r1 r2
  rw [hstep, quadruple_sum_mul F1 F2
    (fun p1 r1 => ZMod.stdAddChar (N := q1)
      (((Nat.gcdB q1 q2 : ℤ) : ZMod q1) * (r1 * (p1 * p1 - (n : ZMod q1)))))
    (fun p2 r2 => ZMod.stdAddChar (N := q2)
      (((Nat.gcdA q1 q2 : ℤ) : ZMod q2) * (r2 * (p2 * p2 - (n : ZMod q2)))))]

/-- The coefficient sum equals the `ZMod` unit double sum (the `V` of `V_coprime_mul`). -/
private lemma A2_sum_eq_V (n q : ℕ) (hq : 0 < q) [NeZero q] :
    (∑ p ∈ (Finset.range q).filter (fun p => Nat.Coprime p q),
        U1534.gaussS q p * U1534.ee (-(((p * n : ℕ) : ℝ)) / (q : ℝ)))
      = ∑ y ∈ (Finset.univ : Finset (ZMod q)).filter (fun y => IsUnit y),
          ∑ z ∈ (Finset.univ : Finset (ZMod q)).filter (fun z => IsUnit z),
            ZMod.stdAddChar (N := q) (z * (y * y - (n : ZMod q))) := by
  simp only [neg_div]
  exact (A2_pair_form n q hq).trans (pair_form_zmod n q)

/-- `A2` vanishes at the modulus `0`. -/
private lemma A2_zero_292a (n : ℕ) : U1534.A2 n 0 = 0 := by
  simp [U1534.A2]

/-- LEAF. Page 13 property i, cited from Schwarz Sections 2 and 3.
The Chinese remainder theorem factors A2 at coprime moduli. This is the
algebraic input to display 47, without any estimate or summation. -/
private theorem A2_coprime_mul (n a b : ℕ) (hab : a.Coprime b) :
    U1534.A2 n (a * b) = U1534.A2 n a * U1534.A2 n b := by

  rcases Nat.eq_zero_or_pos a with rfl | hapos
  · have hb : b = 1 := (Nat.coprime_zero_left b).mp hab
    subst hb
    rw [zero_mul, A2_zero_292a, U1534.A2_one, mul_one]
  rcases Nat.eq_zero_or_pos b with rfl | hbpos
  · have ha : a = 1 := (Nat.coprime_zero_right a).mp hab
    subst ha
    rw [mul_zero, A2_zero_292a, U1534.A2_one, one_mul]
  by_cases ha1 : a = 1
  · subst ha1
    rw [one_mul, U1534.A2_one, one_mul]
  by_cases hb1 : b = 1
  · subst hb1
    rw [mul_one, U1534.A2_one, mul_one]
  haveI : NeZero a := ⟨Nat.pos_iff_ne_zero.mp hapos⟩
  haveI : NeZero b := ⟨Nat.pos_iff_ne_zero.mp hbpos⟩
  have hab0 : a * b ≠ 0 := Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne b)
  haveI : NeZero (a * b) := ⟨hab0⟩
  have hmulpos : 0 < a * b := Nat.pos_of_ne_zero hab0
  rw [U1534.A2, U1534.A2, U1534.A2, A2_sum_eq_V n (a * b) hmulpos,
    A2_sum_eq_V n a hapos, A2_sum_eq_V n b hbpos,
    V_coprime_mul n a b hab,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab,
    Nat.totient_mul hab]
  push_cast
  ring


/-- Page 14 displays 46 and 47. Reuse the proved prime coefficient bound. -/
private theorem prime_coefficient_bound (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ‖U1534.A2 n p‖ ≤ 1 / (p : ℝ) + 6 / (p : ℝ) ^ 2 := by
  exact A2_prime_norm_le_inv_add p n

/-- Page 13 property i. Mathlib gives the squarefree product step.
CONDITIONAL on A2_coprime_mul. -/
private theorem squarefree_factorization (n q : ℕ) (hq : Squarefree q) :
    U1534.A2 n q = ∏ p ∈ q.primeFactors, U1534.A2 n p := by
  let f : ArithmeticFunction ℂ := ⟨U1534.A2 n, by simp [U1534.A2]⟩
  have hf : f.IsMultiplicative :=
    ⟨U1534.A2_one n, fun {a b} hab => A2_coprime_mul n a b hab⟩
  exact (hf.prod_primeFactors hq).symm

/-- Page 14 display 47. Multiply the prime bounds using squarefree
support. CONDITIONAL on A2_coprime_mul. -/
private theorem coefficient_product_bound (n q : ℕ) (hq : 0 < q) :
    ‖U1534.A2 n q‖ ≤ (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) / (q : ℝ) := by
  classical
  by_cases hs : Squarefree q
  · rw [squarefree_factorization n q hs, norm_prod]
    calc
      _ ≤ ∏ p ∈ q.primeFactors, ((1 + 6 / (p : ℝ)) / (p : ℝ)) := by
        apply Finset.prod_le_prod₀
        · intro p hp; exact norm_nonneg _
        · intro p hp
          haveI : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
          have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
          convert prime_coefficient_bound p n using 1 <;> field_simp [hp0] <;> ring
      _ = (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) / (q : ℝ) := by
        rw [Finset.prod_div_distrib]
        have he : (∏ p ∈ q.primeFactors, (p : ℝ)) = q := by
          rw [← Nat.cast_prod]
          exact_mod_cast Nat.prod_primeFactors_of_squarefree hs
        rw [he]
  · rw [A2_eq_zero_of_not_squarefree n q hs, norm_zero]
    exact div_nonneg (Finset.prod_nonneg (fun p _ => by positivity)) (Nat.cast_nonneg q)

/-- Crude explicit upper bound for the prime counting function at a prime. -/
private lemma pi_upper (p : ℕ) (hp : p.Prime) :
    (p.primeCounting : ℝ) ≤ 6 * (p:ℝ) / Real.log p := by
  have hp2 : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hL : 0 < Real.log (p:ℝ) := Real.log_pos hp2
  have h := Chebyshev.pi_le_log4_mul_div (x := (p:ℝ)) hp2
  rw [Nat.floor_natCast, Real.log_sqrt hp0.le] at h
  have hsp : 0 < Real.sqrt (p:ℝ) := Real.sqrt_pos.mpr hp0
  have hlogsp : Real.log (Real.sqrt (p:ℝ)) ≤ Real.sqrt (p:ℝ) := by
    have := Real.log_le_sub_one_of_pos hsp
    linarith
  have hlog2 : Real.log (p:ℝ) ≤ 2 * Real.sqrt (p:ℝ) := by
    have hh : Real.log (p:ℝ) = 2 * Real.log (Real.sqrt (p:ℝ)) := by
      rw [Real.log_sqrt hp0.le]; ring
    rw [hh]; linarith
  have hsq : Real.sqrt (p:ℝ) ≤ 2 * (p:ℝ) / Real.log (p:ℝ) := by
    rw [le_div_iff₀ hL]
    nlinarith [Real.sq_sqrt hp0.le, Real.sqrt_nonneg (p:ℝ)]
  have hlog4 : Real.log 4 ≤ 2 := by
    have h4 : (4:ℝ) = 2^2 := by norm_num
    rw [h4, Real.log_pow]
    push_cast
    nlinarith [Real.log_two_lt_d9]
  have hkey : Real.log 4 * (p:ℝ) / (Real.log (p:ℝ) / 2)
      = 2 * Real.log 4 * ((p:ℝ) / Real.log (p:ℝ)) := by
    field_simp
  rw [hkey] at h
  have hnn : (0:ℝ) ≤ (p:ℝ) / Real.log (p:ℝ) := by positivity
  have hstep : 2 * Real.log 4 * ((p:ℝ) / Real.log (p:ℝ)) ≤ 4 * ((p:ℝ) / Real.log (p:ℝ)) := by
    nlinarith
  set t : ℝ := (p:ℝ) / Real.log (p:ℝ) with ht
  have ht0 : 0 ≤ t := hnn
  have hsq' : Real.sqrt (p:ℝ) ≤ 2 * t := by
    rw [ht, ← mul_div_assoc]
    exact hsq
  have hstep' : 2 * Real.log 4 * t ≤ 4 * t := hstep
  have h' : (p.primeCounting : ℝ) ≤ 2 * Real.log 4 * t + Real.sqrt (p:ℝ) := h
  calc (p.primeCounting : ℝ) ≤ 2 * Real.log 4 * t + Real.sqrt (p:ℝ) := h'
    _ ≤ 4 * t + 2 * t := by linarith [hstep', hsq']
    _ = 6 * t := by ring
    _ = 6 * (p:ℝ) / Real.log p := by rw [ht]; ring

/-- The counting function times a shifted logarithm is linearly bounded at primes. -/
private lemma pi_log_le (p : ℕ) (hp : p.Prime) :
    (p.primeCounting : ℝ) * Real.log ((p.primeCounting : ℝ) + 1) ≤ 12 * (p:ℝ) := by
  have hp2n : 2 ≤ p := hp.two_le
  have hp2 : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hL : 0 < Real.log (p:ℝ) := Real.log_pos hp2
  have h1 : (p.primeCounting : ℝ) ≤ 6 * (p:ℝ) / Real.log p := pi_upper p hp
  have hpi1 : 1 ≤ p.primeCounting := by
    have hne : p.primeCounting ≠ 0 := by
      intro h
      have hle := (Nat.primeCounting_eq_zero_iff).mp h
      omega
    omega
  have hnn : (0:ℝ) ≤ (p.primeCounting : ℝ) := by positivity
  have hcard : p.primeCounting ≤ p + 1 := by
    have hsub : Nat.primesLE p ⊆ Finset.range (p+1) := by
      intro x hx
      rw [Nat.mem_primesLE] at hx
      simp only [Finset.mem_range]
      omega
    have hc := Finset.card_le_card hsub
    simpa using hc
  have hp2r : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2n
  have hsq : (p.primeCounting : ℝ) + 1 ≤ (p:ℝ)^2 := by
    have hc : (p.primeCounting : ℝ) ≤ (p:ℝ) + 1 := by exact_mod_cast hcard
    nlinarith
  have hlog0 : 0 < (p.primeCounting : ℝ) + 1 := by linarith
  have hlog : Real.log ((p.primeCounting : ℝ) + 1) ≤ 2 * Real.log (p:ℝ) := by
    have h := Real.log_le_log hlog0 hsq
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hlog0' : 0 ≤ Real.log ((p.primeCounting : ℝ) + 1) := Real.log_nonneg (by linarith)
  calc (p.primeCounting : ℝ) * Real.log ((p.primeCounting : ℝ) + 1)
      ≤ (6 * (p:ℝ) / Real.log p) * (2 * Real.log (p:ℝ)) := by
        apply mul_le_mul h1 hlog hlog0' (by positivity)
    _ = 12 * (p:ℝ) := by
        field_simp
        ring

/-- Sum of reciprocal primes over a finite set of primes, compared with a loglog sum. -/
private lemma sum_inv_prime_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∑ p ∈ S, 1/(p:ℝ)) ≤
      12 * ∑ i ∈ Finset.range (S.card + 1), 1/((i:ℝ) * Real.log ((i:ℝ)+1)) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a.Prime := hS a (Finset.mem_insert_self a s)
    have hs : ∀ p ∈ s, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hnotmem : a ∉ s := fun h => absurd (hlt a h) (lt_irrefl a)
    have ihs := ih hs
    have hcard : (insert a s).card = s.card + 1 := Finset.card_insert_of_notMem hnotmem
    rw [Finset.sum_insert hnotmem]
    have hrange : (insert a s).card + 1 = (s.card + 1) + 1 := by rw [hcard]
    rw [hrange, Finset.sum_range_succ]
    have ha0 : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha.pos
    have hkpos : (0:ℝ) < ((s.card+1 : ℕ):ℝ) := by
      have : 0 < s.card + 1 := Nat.succ_pos _
      exact_mod_cast this
    have hX0 : (0:ℝ) < ((s.card+1 : ℕ):ℝ) * Real.log (((s.card+1 : ℕ):ℝ)+1) := by
      apply mul_pos hkpos
      apply Real.log_pos
      have : (1:ℝ) < ((s.card+1 : ℕ):ℝ) + 1 := by push_cast; linarith
      linarith
    have hsub : insert a s ⊆ Nat.primesLE a := by
      intro x hx
      rw [Nat.mem_primesLE]
      rcases Finset.mem_insert.mp hx with rfl | hxs
      · exact ⟨le_rfl, ha⟩
      · exact ⟨le_of_lt (hlt x hxs), hs x hxs⟩
    have hcardle : s.card + 1 ≤ a.primeCounting := by
      rw [← hcard]
      calc (insert a s).card ≤ (Nat.primesLE a).card := Finset.card_le_card hsub
        _ = a.primeCounting := Nat.primesLE_card_eq_primeCounting a
    have hb1 : ((s.card+1 : ℕ):ℝ) * Real.log (((s.card+1 : ℕ):ℝ)+1) ≤ 12*(a:ℝ) := by
      have hk : ((s.card+1 : ℕ):ℝ) ≤ (a.primeCounting:ℝ) := by exact_mod_cast hcardle
      have hlogle : Real.log (((s.card+1 : ℕ):ℝ)+1) ≤ Real.log ((a.primeCounting:ℝ)+1) := by
        apply Real.log_le_log
        · have : (0:ℝ) < ((s.card+1:ℕ):ℝ) + 1 := by push_cast; linarith
          linarith
        · linarith
      have hlg0 : 0 ≤ Real.log (((s.card+1 : ℕ):ℝ)+1) := Real.log_nonneg (by push_cast; linarith)
      calc ((s.card+1 : ℕ):ℝ) * Real.log (((s.card+1 : ℕ):ℝ)+1)
          ≤ (a.primeCounting:ℝ) * Real.log ((a.primeCounting:ℝ)+1) := by
            apply mul_le_mul hk hlogle hlg0 (by positivity)
        _ ≤ 12*(a:ℝ) := pi_log_le a ha
    have hstep : 1/(a:ℝ) ≤ 12 * (1/(((s.card+1 : ℕ):ℝ) * Real.log (((s.card+1 : ℕ):ℝ)+1))) := by
      rw [mul_one_div, div_le_div_iff₀ ha0 hX0]
      have hb1' : 1 * (((s.card+1 : ℕ):ℝ) * Real.log (((s.card+1 : ℕ):ℝ)+1)) ≤ 12 * (a:ℝ) := by
        linarith
      exact hb1'
    nlinarith [ihs, hstep]

/-- A first-order lower bound for `log x - log y`. -/
private lemma log_sub_log_ge (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : y ≤ x) :
    (x - y)/x ≤ Real.log x - Real.log y := by
  have hpos : 0 < y/x := by positivity
  have h := Real.log_le_sub_one_of_pos hpos
  rw [Real.log_div hy.ne' hx.ne'] at h
  have h2 : y/x - 1 = (y - x)/x := by field_simp
  rw [h2] at h
  have h3 : 1 - y/x = (x - y)/x := by field_simp
  linarith

/-- One step of the loglog telescoping. -/
private lemma inv_log_step (j : ℕ) (hj : 2 ≤ j) :
    1/(((j+1:ℕ):ℝ) * Real.log (((j+1:ℕ):ℝ))) ≤
      Real.log (Real.log (((j+1:ℕ):ℝ))) - Real.log (Real.log ((j:ℝ))) := by
  have hj2 : (2:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
  have hj0 : (0:ℝ) < (j:ℝ) := by linarith
  have hj10 : (0:ℝ) < (j:ℝ) + 1 := by linarith
  have hbj : 0 < Real.log (j:ℝ) := Real.log_pos (by linarith)
  have haj : 0 < Real.log ((j:ℝ)+1) := Real.log_pos (by linarith)
  push_cast
  have hb0 : (0:ℝ) < Real.log (j:ℝ) := hbj
  have step1 : 1/((j:ℝ)+1) ≤ Real.log ((j:ℝ)+1) - Real.log (j:ℝ) := by
    have h := log_sub_log_ge ((j:ℝ)+1) (j:ℝ) hj10 hj0 (by linarith)
    convert h using 2 <;> ring
  have step2 : (Real.log ((j:ℝ)+1) - Real.log (j:ℝ))/Real.log ((j:ℝ)+1)
      ≤ Real.log (Real.log ((j:ℝ)+1)) - Real.log (Real.log (j:ℝ)) :=
    log_sub_log_ge (Real.log ((j:ℝ)+1)) (Real.log (j:ℝ)) haj hbj
      (Real.log_le_log hj0 (by linarith))
  calc 1/(((j:ℝ)+1) * Real.log ((j:ℝ)+1))
      = (1/((j:ℝ)+1))/Real.log ((j:ℝ)+1) := by field_simp
    _ ≤ (Real.log ((j:ℝ)+1) - Real.log (j:ℝ))/Real.log ((j:ℝ)+1) := by
        apply div_le_div_of_nonneg_right step1 haj.le
    _ ≤ _ := step2


/-- The tail reciprocal-log sum telescopes against `log log`. -/
private lemma range_H_le (k : ℕ) (hk : 2 ≤ k) :
    (∑ i ∈ Finset.range (k-2), 1/(((3+i:ℕ):ℝ) * Real.log ((3+i:ℕ):ℝ)))
      ≤ Real.log (Real.log (k:ℝ)) - Real.log (Real.log 2) := by
  have hsub := Finset.sum_range_sub (fun i : ℕ => Real.log (Real.log (((i+2:ℕ)):ℝ))) (n := k-2)
  have hstep : ∀ i ∈ Finset.range (k-2),
      1/(((3+i:ℕ):ℝ) * Real.log ((3+i:ℕ):ℝ))
        ≤ Real.log (Real.log (((i+1)+2:ℕ):ℝ)) - Real.log (Real.log (((i+2:ℕ)):ℝ)) := by
    intro i _
    have h := inv_log_step (i+2) (by omega)
    have e1 : ((i+2:ℕ)+1) = (3+i : ℕ) := by omega
    rw [e1] at h
    have e2 : ((i+1)+2 : ℕ) = (3+i : ℕ) := by omega
    rw [e2]
    exact h
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [hsub]
  have e3 : k - 2 + 2 = k := by omega
  rw [e3]
  norm_num


/-- The reciprocal-log sum over `range (k+1)`. -/
private lemma V_bound (k : ℕ) (hk : 2 ≤ k) :
    (∑ i ∈ Finset.range (k+1), 1/((i:ℝ) * Real.log ((i:ℝ)+1)))
      ≤ Real.log (Real.log (k:ℝ)) + 4 := by
  have hlog2 : (0:ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  set a : ℕ → ℝ := fun i => 1/((i:ℝ) * Real.log ((i:ℝ)+1)) with ha
  set b : ℕ → ℝ := fun i => 1/((i:ℝ) * Real.log (i:ℝ)) with hb
  have hsplit := Finset.sum_range_add a 2 (k-1)
  rw [show 2 + (k-1) = k + 1 by omega] at hsplit
  rw [hsplit]
  have hfirst : (∑ x ∈ Finset.range 2, a x) = 1/Real.log 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp only [ha]
    norm_num
  rw [hfirst]
  have hshift : ∀ x ∈ Finset.range (k-1), a (2+x) ≤ b (2+x) := by
    intro x hx
    simp only [ha, hb]
    push_cast
    have hx0 : (0:ℝ) < 2 + (x:ℝ) := by positivity
    have hlogx : 0 < Real.log (2 + (x:ℝ)) := Real.log_pos (by linarith)
    have hlogx1 : Real.log (2 + (x:ℝ)) ≤ Real.log (2 + (x:ℝ) + 1) :=
      Real.log_le_log hx0 (by linarith)
    have hd1 : (0:ℝ) < (2 + (x:ℝ)) * Real.log (2 + (x:ℝ) + 1) :=
      mul_pos hx0 (Real.log_pos (by linarith))
    have hd2 : (0:ℝ) < (2 + (x:ℝ)) * Real.log (2 + (x:ℝ)) := mul_pos hx0 hlogx
    rw [div_le_div_iff₀ hd1 hd2]
    nlinarith [hlogx1, hx0]
  have hbound1 : (∑ x ∈ Finset.range (k-1), a (2+x)) ≤ ∑ x ∈ Finset.range (k-1), b (2+x) :=
    Finset.sum_le_sum hshift
  have hAB : 1/Real.log 2 + (∑ x ∈ Finset.range (k-1), a (2+x))
      ≤ 1/Real.log 2 + ∑ x ∈ Finset.range (k-1), b (2+x) := by linarith
  refine hAB.trans ?_
  have hsplit2 : (∑ x ∈ Finset.range (k-1), b (2+x))
      = (∑ x ∈ Finset.range 1, b (2+x)) + ∑ x ∈ Finset.range (k-2), b (2+(1+x)) := by
    have hrw2 : k - 1 = 1 + (k-2) := by omega
    conv_lhs => rw [hrw2]
    exact Finset.sum_range_add (fun x => b (2+x)) 1 (k-2)
  rw [hsplit2]
  have hb1 : (∑ x ∈ Finset.range 1, b (2+x)) = 1/((2:ℝ) * Real.log 2) := by
    rw [Finset.sum_range_one]
    simp only [hb]
    norm_num
  rw [hb1]
  have hb2 : (∑ x ∈ Finset.range (k-2), b (2+(1+x)))
      = ∑ x ∈ Finset.range (k-2), 1/(((3+x:ℕ):ℝ) * Real.log ((3+x:ℕ):ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro x _
    simp only [hb]
    have e : (2+(1+x:ℕ)) = (3+x : ℕ) := by omega
    rw [e]
  rw [hb2]
  have hH := range_H_le k hk
  have hA : 1/Real.log 2 ≤ 2 := by
    rw [div_le_iff₀ hlog2]
    have := Real.log_two_gt_d9; linarith
  have hB : 1/((2:ℝ) * Real.log 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have := Real.log_two_gt_d9; linarith
  have hC : -Real.log (Real.log 2) ≤ 1 := by
    have hp : (0:ℝ) < 1/Real.log 2 := by positivity
    have h := Real.log_le_sub_one_of_pos hp
    rw [Real.log_div one_ne_zero hlog2.ne'] at h
    simp only [Real.log_one] at h
    linarith
  linarith [hH]

/-- The reciprocal-log sum is at most four for a very small number of primes. -/
private lemma V_le_four (k : ℕ) (hk : k ≤ 1) :
    (∑ i ∈ Finset.range (k+1), 1/((i:ℝ) * Real.log ((i:ℝ)+1))) ≤ 4 := by
  have hlog2 : (0:ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  interval_cases k
  · norm_num
  · have hsum : (∑ i ∈ Finset.range (1+1), 1/((i:ℝ) * Real.log ((i:ℝ)+1))) = 1/Real.log 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      norm_num
    rw [hsum, div_le_iff₀ hlog2]
    have := Real.log_two_gt_d9
    linarith

/-- The core bound: the square of the local majorant is at most a constant times `log q + 2`. -/
private lemma core (q : ℕ) (hq : 1 ≤ q) :
    (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) ^ 2 ≤
      Real.exp 576 * ((Nat.factorial 144 : ℕ) : ℝ) * 2 * (Real.log (q:ℝ) + 2) := by
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  set k : ℕ := q.primeFactors.card with hk
  have hfpos : 0 < (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) := by
    exact Finset.prod_pos (fun p hp => by positivity)
  have hlogf : Real.log ((∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))))
      = ∑ p ∈ q.primeFactors, Real.log (1 + 6/(p:ℝ)) := by
    exact Real.log_prod (fun p hp => by positivity)
  have hterm : ∀ p ∈ q.primeFactors, Real.log (1 + 6/(p:ℝ)) ≤ 6 * (1/(p:ℝ)) := by
    intro p hp
    have hp2 : (2:ℝ) ≤ (p:ℝ) := by
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      exact_mod_cast this
    have hpos : (0:ℝ) < 1 + 6/(p:ℝ) := by positivity
    have h := Real.log_le_sub_one_of_pos hpos
    have heq : 1 + 6/(p:ℝ) - 1 = 6/(p:ℝ) := by ring
    rw [heq] at h
    rw [mul_one_div]
    exact h
  have hsum_le : Real.log ((∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ)))) ≤ 6 * ∑ p ∈ q.primeFactors, 1/(p:ℝ) := by
    rw [hlogf, Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hsum12 : (∑ p ∈ q.primeFactors, 1/(p:ℝ))
      ≤ 12 * ∑ i ∈ Finset.range (k+1), 1/((i:ℝ) * Real.log ((i:ℝ)+1)) := by
    rw [hk]
    exact sum_inv_prime_le q.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  by_cases hk1 : k ≤ 1
  · -- few primes
    have hV : (∑ i ∈ Finset.range (k+1), 1/((i:ℝ) * Real.log ((i:ℝ)+1))) ≤ 4 := V_le_four k hk1
    have hf : (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) ≤ Real.exp 288 := by
      have h1 : Real.log ((∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ)))) ≤ 288 := by
        have := hsum_le.trans (mul_le_mul_of_nonneg_left (hsum12.trans (mul_le_mul_of_nonneg_left hV (by norm_num))) (by norm_num : (0:ℝ) ≤ 6))
        linarith
      calc (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) ≤ Real.exp (Real.log ((∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))))) := (Real.exp_log hfpos).ge
        _ ≤ Real.exp 288 := Real.exp_le_exp.mpr h1
    have hsq : (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) ^ 2 ≤ Real.exp 576 := by
      have := pow_le_pow_left₀ hfpos.le hf 2
      calc (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) ^ 2 ≤ (Real.exp 288)^2 := this
        _ = Real.exp 576 := by
            rw [← Real.exp_nat_mul]
            norm_num
    have hK4 : Real.exp 576 ≤ Real.exp 576 * ((Nat.factorial 144 : ℕ) : ℝ) * 2 * 2 := by
      have h1 : (1:ℝ) ≤ ((Nat.factorial 144 : ℕ) : ℝ) := by
        have : 1 ≤ Nat.factorial 144 := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero 144)
        exact_mod_cast this
      have := Real.exp_pos 576
      nlinarith
    have h2 : (2:ℝ) ≤ Real.log (q:ℝ) + 2 := by
      have : 0 ≤ Real.log (q:ℝ) := Real.log_nonneg (by exact_mod_cast hq)
      linarith
    calc (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) ^ 2 ≤ Real.exp 576 := hsq
      _ ≤ Real.exp 576 * ((Nat.factorial 144 : ℕ) : ℝ) * 2 * 2 := hK4
      _ ≤ Real.exp 576 * ((Nat.factorial 144 : ℕ) : ℝ) * 2 * (Real.log (q:ℝ) + 2) := by
          have h1 : (0:ℝ) ≤ Real.exp 576 * ((Nat.factorial 144 : ℕ) : ℝ) * 2 := by positivity
          exact mul_le_mul_of_nonneg_left h2 h1
  · -- at least two primes
    have hk2 : 2 ≤ k := by omega
    have hV : (∑ i ∈ Finset.range (k+1), 1/((i:ℝ) * Real.log ((i:ℝ)+1)))
        ≤ Real.log (Real.log (k:ℝ)) + 4 := V_bound k hk2
    have hkr : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
    have hlogk : 0 < Real.log (k:ℝ) := Real.log_pos (by linarith)
    -- k <= 2 log q
    have h2k : (2:ℕ)^k ≤ q := by
      have hdvd := Nat.prod_primeFactors_dvd q
      have hle : ∏ p ∈ q.primeFactors, p ≤ q := Nat.le_of_dvd (by omega) hdvd
      have h2 : (2:ℕ)^k ≤ ∏ p ∈ q.primeFactors, p := by
        rw [← Finset.prod_const]
        exact Finset.prod_le_prod (fun p hp => Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp))
      exact h2.trans hle
    have hklq : (k:ℝ) ≤ 2 * Real.log (q:ℝ) := by
      have h1 : ((2:ℕ)^k : ℝ) ≤ (q:ℝ) := by exact_mod_cast h2k
      have h2 : ((2:ℕ)^k : ℝ) = (2:ℝ)^k := by push_cast; ring
      rw [h2] at h1
      have h3 : Real.log ((2:ℝ)^k) ≤ Real.log (q:ℝ) :=
        Real.log_le_log (by positivity) h1
      rw [Real.log_pow] at h3
      have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by
        have := Real.log_two_gt_d9; linarith
      nlinarith
    -- exponential chain
    have hlogf_le : Real.log ((∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ)))) ≤ 72 * Real.log (Real.log (k:ℝ)) + 288 := by
      have hA : 6 * ∑ p ∈ q.primeFactors, 1/(p:ℝ) ≤ 72 * (Real.log (Real.log (k:ℝ)) + 4) := by
        have := hsum12.trans (mul_le_mul_of_nonneg_left hV (by norm_num : (0:ℝ) ≤ 12))
        nlinarith
      linarith
    have hexp : Real.exp (72 * Real.log (Real.log (k:ℝ)) + 288)
        = Real.exp 288 * (Real.log (k:ℝ))^72 := by
      rw [Real.exp_add]
      have hc : (72:ℝ) = ((72:ℕ):ℝ) := by norm_num
      have h : Real.exp (72 * Real.log (Real.log (k:ℝ))) = (Real.log (k:ℝ))^72 := by
        rw [hc, Real.exp_nat_mul, Real.exp_log hlogk]
      rw [h]
      ring
    have hf : (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) ≤ Real.exp 288 * (Real.log (k:ℝ))^72 := by
      have := (Real.log_le_iff_le_exp hfpos).mp hlogf_le
      rwa [hexp] at this
    have hf2 : (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) ^ 2 ≤ Real.exp 576 * (Real.log (k:ℝ))^144 := by
      have := pow_le_pow_left₀ (le_of_lt hfpos) hf 2
      calc (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) ^ 2 ≤ (Real.exp 288 * (Real.log (k:ℝ))^72)^2 := this
        _ = Real.exp 576 * (Real.log (k:ℝ))^144 := by
            rw [mul_pow, ← pow_mul, ← Real.exp_nat_mul]
            norm_num
    have hfac : (Real.log (k:ℝ))^144 ≤ ((Nat.factorial 144 : ℕ) : ℝ) * (k:ℝ) := by
      have h := Real.pow_div_factorial_le_exp (Real.log (k:ℝ)) hlogk.le 144
      rw [Real.exp_log (by linarith : (0:ℝ) < (k:ℝ))] at h
      rw [div_le_iff₀ (by positivity : (0:ℝ) < ((Nat.factorial 144 : ℕ) : ℝ))] at h
      linarith
    calc (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) ^ 2 ≤ Real.exp 576 * (Real.log (k:ℝ))^144 := hf2
      _ ≤ Real.exp 576 * (((Nat.factorial 144 : ℕ) : ℝ) * (k:ℝ)) := by
          exact mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = Real.exp 576 * ((Nat.factorial 144 : ℕ) : ℝ) * 2 * ((k:ℝ)/2) := by ring
      _ ≤ Real.exp 576 * ((Nat.factorial 144 : ℕ) : ℝ) * 2 * (Real.log (q:ℝ)) := by
          have h1 : (0:ℝ) ≤ Real.exp 576 * ((Nat.factorial 144 : ℕ) : ℝ) * 2 := by positivity
          have hklq2 : (k:ℝ)/2 ≤ Real.log (q:ℝ) := by linarith
          exact mul_le_mul_of_nonneg_left hklq2 h1
      _ ≤ Real.exp 576 * ((Nat.factorial 144 : ℕ) : ℝ) * 2 * (Real.log (q:ℝ) + 2) := by
          have h1 : (0:ℝ) ≤ Real.exp 576 * ((Nat.factorial 144 : ℕ) : ℝ) * 2 := by positivity
          have h2 : Real.log (q:ℝ) ≤ Real.log (q:ℝ) + 2 := by linarith
          exact mul_le_mul_of_nonneg_left h2 h1

/-- LEAF. Page 14 display 47 and page 15 first display. The square of the
local product is bounded by C log x for q at most x to the one third.
This leaf has no A2 coefficient and no interval sum. -/
private theorem localMajorant_log_bound :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ (x : ℝ) (q : ℕ),
      x0 ≤ x → 0 < q → (q : ℝ) ≤ x ^ (1 / 3 : ℝ) →
      (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) ^ 2 ≤ C * Real.log x := by

  refine ⟨Real.exp 576 * ((Nat.factorial 144 : ℕ) : ℝ) * 2, 100, by positivity, by norm_num, ?_⟩
  intro x q hx hq hqle
  have hx100 : (100:ℝ) ≤ x := hx
  have hx0 : (0:ℝ) < x := by linarith
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hcore := core q (by omega)
  have hlog100 : (3:ℝ) ≤ Real.log 100 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 100)]
    have h1 : Real.exp 3 = (Real.exp 1)^3 := by
      rw [show (3:ℝ) = ((3:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
    rw [h1]
    have he : Real.exp 1 < 2.72 := by linarith [Real.exp_one_lt_d9]
    have he0 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
    have h3 : (Real.exp 1)^3 ≤ (2.72:ℝ)^3 := pow_le_pow_left₀ he0.le he.le 3
    have h272 : (2.72:ℝ)^3 < 100 := by norm_num
    linarith
  have hlogx3 : (3:ℝ) ≤ Real.log x :=
    hlog100.trans (Real.log_le_log (by norm_num) hx100)
  have hlogq : Real.log (q:ℝ) ≤ Real.log x / 3 := by
    have h := Real.log_le_log hq0 hqle
    rw [Real.log_rpow hx0] at h
    linarith
  have h2 : Real.log (q:ℝ) + 2 ≤ Real.log x := by linarith
  refine hcore.trans ?_
  exact mul_le_mul_of_nonneg_left h2 (by positivity)


/-- LEAF. Page 15 first display. Real cutoff reciprocal square tail.
The already proved sum_inv_sq_Ioc_le handles positive natural cutoffs. -/
private theorem reciprocal_square_tail (P : ℝ) (b : ℕ) (hP : 0 < P) :
    (∑ q ∈ Finset.Ioc ⌊P⌋₊ b, 1 / (q : ℝ) ^ 2) ≤ 2 / P := by
  by_cases h : 0 < ⌊P⌋₊ ∧ ⌊P⌋₊ ≤ b
  · rcases h with ⟨hP0, hPb⟩
    have h1 := sum_inv_sq_Ioc_le ⌊P⌋₊ b hP0 hPb
    calc
      (∑ q ∈ Finset.Ioc ⌊P⌋₊ b, 1 / (q : ℝ) ^ 2) ≤ 1 / (⌊P⌋₊ : ℝ) - 1 / (b : ℝ) := h1
      _ ≤ 1 / (⌊P⌋₊ : ℝ) := sub_le_self _ (by positivity)
      _ ≤ 2 / P := by
        have hd : P < 2 * ⌊P⌋₊ := by
          have hpfloor : 1 ≤ (⌊P⌋₊ : ℝ) := Nat.one_le_cast.mpr hP0
          have : P < (⌊P⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one P
          linarith
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
  · push Not at h
    by_cases hP0 : 0 < ⌊P⌋₊
    · have hbb : b < ⌊P⌋₊ := h hP0
      have : Finset.Ioc ⌊P⌋₊ b = ∅ := Finset.Ioc_eq_empty_of_le (le_of_lt hbb)
      rw [this, Finset.sum_empty]
      positivity
    · have hP0' : ⌊P⌋₊ = 0 := by omega
      have hp1 : P < 1 := Nat.floor_eq_zero.mp hP0'
      by_cases hb : 0 < b
      · have : Finset.Ioc ⌊P⌋₊ b = Finset.Ioc 0 b := by rw [hP0']
        rw [this]
        have h_eq : Finset.Ioc 0 b = insert 1 (Finset.Ioc 1 b) := by
          ext x
          simp only [Finset.mem_Ioc, Finset.mem_insert]
          omega
        rw [h_eq, Finset.sum_insert (by simp)]
        have h_sum : (∑ q ∈ Finset.Ioc 1 b, 1 / (q : ℝ) ^ 2) ≤ 1 / (1 : ℝ) - 1 / (b : ℝ) := by
          exact_mod_cast sum_inv_sq_Ioc_le 1 b (by omega) (by omega)
        calc
          1 / ((1 : ℕ) : ℝ) ^ 2 + ∑ q ∈ Finset.Ioc 1 b, 1 / (q : ℝ) ^ 2 ≤ 1 + (1 / (1 : ℝ) - 1 / (b : ℝ)) := by
            have : 1 / ((1 : ℕ) : ℝ) ^ 2 = 1 := by norm_num
            rw [this]
            exact add_le_add le_rfl h_sum
          _ ≤ 2 := by linarith [show 0 ≤ 1 / (b : ℝ) by positivity]
          _ ≤ 2 / P := by
            rw [le_div_iff₀ hP]
            linarith
      · have : b = 0 := by omega
        have : Finset.Ioc ⌊P⌋₊ b = ∅ := by rw [this, hP0']; exact Finset.Ioc_eq_empty_of_le le_rfl
        rw [this, Finset.sum_empty]
        positivity


/-- Conjugation acts on `ee t = exp(2 π i t)` by `t ↦ -t`. -/
private lemma conj_ee (t : ℝ) : (starRingEnd ℂ) (U1534.ee t) = U1534.ee (-t) := by
  simp only [U1534.ee]
  rw [← Complex.exp_conj]
  have harg : (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) =
      2 * (Real.pi : ℂ) * Complex.I * ((-t : ℝ) : ℂ) := by
    rw [map_mul, map_mul, map_mul]
    simp only [map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [harg]

/-- `ee` is unchanged by adding an integer to its argument. -/
private lemma ee_add_int (t : ℝ) (k : ℤ) : U1534.ee (t + (k : ℝ)) = U1534.ee t := by
  simp only [U1534.ee]
  have harg : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (((t + (k : ℝ)) : ℝ) : ℂ) =
      (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (t : ℂ) + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Conjugating a Gauss sum complements the additive character's frequency. -/
private lemma conj_gaussS {q a : ℕ} (ha : a ≤ q) :
    (starRingEnd ℂ) (U1534.gaussS q a) = U1534.gaussS q (q - a) := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    simp [U1534.gaussS]
  · simp only [U1534.gaussS]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [conj_ee]
    have h1 : ((a * x ^ 2 : ℕ) : ℝ) = (a : ℝ) * (x : ℝ) ^ 2 := by
      push_cast
      ring
    have h2 : (((q - a) * x ^ 2 : ℕ) : ℝ) = (q : ℝ) * (x : ℝ) ^ 2 - (a : ℝ) * (x : ℝ) ^ 2 := by
      rw [Nat.sub_mul, Nat.cast_sub (Nat.mul_le_mul_right _ ha), Nat.cast_mul, Nat.cast_mul]
      push_cast
      ring
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have hkey : -(↑(a * x ^ 2) / (q : ℝ)) =
        ↑((q - a) * x ^ 2) / (q : ℝ) + ((-(x ^ 2 : ℤ) : ℤ) : ℝ) := by
      rw [h1, h2]
      push_cast
      field_simp
      ring
    rw [hkey, ee_add_int]

/-- The residue set `{a < q : (a,q) = 1}` is stable under `a ↦ q - a`. -/
private lemma coprime_residues_image {q : ℕ} (hq : 2 ≤ q) :
    ((Finset.range q).filter (fun a => Nat.Coprime a q)).image (fun a => q - a) =
      (Finset.range q).filter (fun a => Nat.Coprime a q) := by
  have hmem : ∀ a, a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) ↔
      a < q ∧ Nat.Coprime a q := by
    intro a
    simp
  have hpos : ∀ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), 0 < a := by
    intro a ha
    have ha' := (hmem a).mp ha
    rcases Nat.eq_zero_or_pos a with h0 | h
    · exfalso
      subst h0
      have : q = 1 := by simpa using ha'.2
      omega
    · exact h
  apply Finset.Subset.antisymm
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    refine (hmem _).mpr ⟨Nat.sub_lt (by omega) (hpos a ha), ?_⟩
    exact (Nat.coprime_self_sub_left (le_of_lt ((hmem a).mp ha).1)).mpr ((hmem a).mp ha).2
  · intro b hb
    refine Finset.mem_image.mpr ⟨q - b, ?_, ?_⟩
    · refine (hmem _).mpr ⟨Nat.sub_lt (by omega) (hpos b hb), ?_⟩
      exact (Nat.coprime_self_sub_left (le_of_lt ((hmem b).mp hb).1)).mpr ((hmem b).mp hb).2
    · exact Nat.sub_sub_self (le_of_lt ((hmem b).mp hb).1)

/-- LEAF. Page 13 display 45 and property v, used on page 15 after
 display 51. Pairing a with minus a makes A2 real. This algebraic leaf
contains no estimate and applies to every natural modulus. -/
private theorem A2_conj (n q : ℕ) :
    (starRingEnd ℂ) (U1534.A2 n q) = U1534.A2 n q := by
  rcases Nat.lt_or_ge q 2 with hq | hq
  · interval_cases q <;> simp [U1534.A2, U1534.gaussS, U1534.ee]
  · set A : Finset ℕ := (Finset.range q).filter (fun a => Nat.Coprime a q) with hA
    have hmemA : ∀ a, a ∈ A ↔ a < q ∧ Nat.Coprime a q := by
      intro a
      rw [hA]
      simp
    have hposA : ∀ a ∈ A, 0 < a := by
      intro a ha
      have ha' := (hmemA a).mp ha
      rcases Nat.eq_zero_or_pos a with h0 | h
      · exfalso
        subst h0
        have : q = 1 := by simpa using ha'.2
        omega
      · exact h
    have hq0 : (q : ℝ) ≠ 0 := by
      have : 0 < q := by omega
      exact_mod_cast this.ne'
    have himageA : A.image (fun a => q - a) = A := by
      rw [hA]
      exact coprime_residues_image hq
    -- expand `A2` along `A`
    have hA2 : U1534.A2 n q =
        ((ArithmeticFunction.moebius q : ℤ) : ℂ) / ((Nat.totient q : ℂ) ^ 2) *
          ∑ a ∈ A, U1534.gaussS q a * U1534.ee (-(((a * n : ℕ) : ℝ) / (q : ℝ))) := by
      simp only [U1534.A2, neg_div]
      rw [← hA]
    -- conjugation of the inner sum
    have hconjS : (starRingEnd ℂ)
        (∑ a ∈ A, U1534.gaussS q a * U1534.ee (-(((a * n : ℕ) : ℝ) / (q : ℝ)))) =
        ∑ a ∈ A, U1534.gaussS q (q - a) * U1534.ee ((((a * n : ℕ) : ℝ) / (q : ℝ))) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [map_mul, conj_gaussS (le_of_lt ((hmemA a).mp ha).1), conj_ee]
      simp
    -- reindex `a ↦ q - a`
    have hshift : (∑ a ∈ A, U1534.gaussS q (q - a) * U1534.ee ((((a * n : ℕ) : ℝ) / (q : ℝ)))) =
        ∑ b ∈ A, U1534.gaussS q b * U1534.ee (((((q - b) * n : ℕ) : ℝ) / (q : ℝ))) := by
      refine Finset.sum_bij (fun a _ => q - a) ?_ ?_ ?_ ?_
      · intro a ha
        refine (hmemA _).mpr ⟨Nat.sub_lt (by omega) (hposA a ha), ?_⟩
        exact (Nat.coprime_self_sub_left (le_of_lt ((hmemA a).mp ha).1)).mpr ((hmemA a).mp ha).2
      · intro a1 ha1 a2 ha2 heq
        have h1 := congrArg (fun t => q - t) heq
        rwa [Nat.sub_sub_self (le_of_lt ((hmemA a1).mp ha1).1),
          Nat.sub_sub_self (le_of_lt ((hmemA a2).mp ha2).1)] at h1
      · intro b hb
        refine ⟨q - b, (hmemA _).mpr ⟨Nat.sub_lt (by omega) (hposA b hb), ?_⟩,
          Nat.sub_sub_self (le_of_lt ((hmemA b).mp hb).1)⟩
        exact (Nat.coprime_self_sub_left (le_of_lt ((hmemA b).mp hb).1)).mpr ((hmemA b).mp hb).2
      · intro a ha
        rw [Nat.sub_sub_self (le_of_lt ((hmemA a).mp ha).1)]
    -- shift the character back by an integer
    have hback : (∑ b ∈ A, U1534.gaussS q b * U1534.ee (((((q - b) * n : ℕ) : ℝ) / (q : ℝ)))) =
        ∑ b ∈ A, U1534.gaussS q b * U1534.ee (-(((b * n : ℕ) : ℝ) / (q : ℝ))) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hbq : b ≤ q := le_of_lt ((hmemA b).mp hb).1
      have hcast : (((q - b) * n : ℕ) : ℝ) = (q : ℝ) * (n : ℝ) - (b : ℝ) * (n : ℝ) := by
        rw [Nat.sub_mul, Nat.cast_sub (Nat.mul_le_mul_right n hbq), Nat.cast_mul, Nat.cast_mul]
      have hkey : ((q : ℝ) * (n : ℝ) - (b : ℝ) * (n : ℝ)) / (q : ℝ) =
          -(((b : ℝ) * (n : ℝ)) / (q : ℝ)) + ((n : ℤ) : ℝ) := by
        field_simp
        push_cast
        ring
      rw [hcast, hkey, ee_add_int, Nat.cast_mul]
    -- conjugation of the real prefactor
    have hc : (starRingEnd ℂ) (((ArithmeticFunction.moebius q : ℤ) : ℂ) /
        ((Nat.totient q : ℂ) ^ 2)) =
        ((ArithmeticFunction.moebius q : ℤ) : ℂ) / ((Nat.totient q : ℂ) ^ 2) := by
      simp
    rw [hA2, map_mul, hc, hconjS, hshift, hback]

/-- Page 15 second display. The conjugated interval estimate follows
from the already proved unconjugated estimate. CONDITIONAL on A2_conj. -/
private theorem A2_conjugate_interval_bound {q r : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hqr : q ≠ r) (a b : ℕ) :
    ‖∑ n ∈ Finset.Ico a b, U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r)‖ ≤
      2 * ∑ n ∈ Finset.range (q * r),
        ‖U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r)‖ := by
  simpa only [A2_conj] using A2_interval_bound hq hr hqr a b

/-- Page 15 second display and page 14 display 47. The coefficient
product bound controls the full period absolute sum. CONDITIONAL on
A2_coprime_mul through coefficient_product_bound. -/
private theorem complete_period_majorant {q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    (∑ n ∈ Finset.range (q * r),
      ‖U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r)‖) ≤
        (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) * (∏ p ∈ r.primeFactors, (1 + 6 / (p : ℝ))) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  calc
    _ ≤ ∑ _n ∈ Finset.range (q * r),
        ((∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) / (q : ℝ)) * ((∏ p ∈ r.primeFactors, (1 + 6 / (p : ℝ))) / (r : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, norm_conj]
      exact mul_le_mul (coefficient_product_bound n q hq)
        (coefficient_product_bound n r hr) (norm_nonneg _)
        ((norm_nonneg _).trans (coefficient_product_bound n q hq))
    _ = (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) * (∏ p ∈ r.primeFactors, (1 + 6 / (p : ℝ))) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_mul]
      field_simp

/-- Pointwise product monotonicity for nonnegative real factors (no `MulLeftMono` for `ℝ`). -/
private lemma prod_le_prod_nonneg {ι : Type*} {s : Finset ι} {f g : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons ha, Finset.prod_cons ha]
    simp only [Finset.mem_cons, forall_eq_or_imp] at h0 h
    have hfs : 0 ≤ ∏ x ∈ s, f x := Finset.prod_nonneg h0.2
    exact mul_le_mul h.1 (ih h0.2 h.2) hfs (h0.1.trans h.1)

/-- A product of factors at least one is at least one. -/
private lemma one_le_prod_nonneg {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons ha]
    simp only [Finset.mem_cons, forall_eq_or_imp] at h
    have h1 := ih h.2
    nlinarith [h.1, h1]

/-- Extending a product by factors at least one increases it. -/
private lemma prod_le_prod_of_subset_nonneg {ι : Type*} {s t : Finset ι} {f : ι → ℝ}
    (hst : s ⊆ t) (h0 : ∀ i ∈ t, 0 ≤ f i) (h1 : ∀ i ∈ t, i ∉ s → 1 ≤ f i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  classical
  have hsplit : ∏ i ∈ t, f i = (∏ i ∈ t \ s, f i) * (∏ i ∈ s, f i) := (Finset.prod_sdiff hst).symm
  have hone : 1 ≤ ∏ i ∈ t \ s, f i :=
    one_le_prod_nonneg (fun i hi => h1 i (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hi).2)
  have hpos : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg (fun i hi => h0 i (hst hi))
  rw [hsplit]
  nlinarith [hone, hpos]

/-- Small primes divide `q` rarely enough that their local factors cost a constant. -/
private lemma localMajorant_small_part (q : ℕ) :
    ∏ p ∈ q.primeFactors.filter (fun p => p < 30), (1 + 6 / (p : ℝ)) ≤ (7 : ℝ) ^ 10 := by
  have h1 : ∀ p ∈ q.primeFactors.filter (fun p => p < 30), (1 + 6 / (p : ℝ)) ≤ 7 := by
    intro p hp
    have hpp : p ∈ q.primeFactors := (Finset.mem_filter.mp hp).1
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      have := Nat.prime_of_mem_primeFactors hpp
      have : 2 ≤ p := this.two_le
      exact_mod_cast this
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have h6 : 6 / (p : ℝ) ≤ 6 := by
      rw [div_le_iff₀ hp0]
      nlinarith
    linarith
  have hstep : ∏ p ∈ q.primeFactors.filter (fun p => p < 30), (1 + 6 / (p : ℝ))
      ≤ ∏ p ∈ q.primeFactors.filter (fun p => p < 30), (7 : ℝ) :=
    prod_le_prod_nonneg (fun i hi => by positivity) h1
  calc ∏ p ∈ q.primeFactors.filter (fun p => p < 30), (1 + 6 / (p : ℝ))
      ≤ ∏ p ∈ q.primeFactors.filter (fun p => p < 30), (7 : ℝ) := hstep
    _ = (7 : ℝ) ^ (q.primeFactors.filter (fun p => p < 30)).card := Finset.prod_const _
    _ ≤ (7 : ℝ) ^ 10 := by
        apply pow_le_pow_right₀ (by norm_num)
        have hsub : q.primeFactors.filter (fun p => p < 30) ⊆ (Finset.range 30).filter Nat.Prime := by
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
          exact ⟨hp.2, Nat.prime_of_mem_primeFactors hp.1⟩
        have hcard := Finset.card_le_card hsub
        have h30 : ((Finset.range 30).filter Nat.Prime).card = 10 := by decide
        omega

/-- A prime at least `30` is dominated by `p ^ (1/8)`. -/
private lemma one_add_six_div_le_eighth {p : ℕ} (hp : 30 ≤ p) :
    1 + 6 / (p : ℝ) ≤ (p : ℝ) ^ ((8 : ℕ) : ℝ)⁻¹ := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : (0 : ℕ) < p := by omega
    exact_mod_cast this
  have hp30 : (30 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hle1 : 1 + 6 / (p : ℝ) ≤ 6 / 5 := by
    have h6 : 6 / (p : ℝ) ≤ 1 / 5 := by
      rw [div_le_iff₀ hp0]
      nlinarith
    linarith
  have hbase : ((6 / 5 : ℝ)) ^ 8 ≤ (p : ℝ) := by
    have hval : ((6 / 5 : ℝ)) ^ 8 = 1679616 / 390625 := by norm_num
    rw [hval]
    nlinarith
  have h2 : (6 / 5 : ℝ) ≤ (p : ℝ) ^ ((8 : ℕ) : ℝ)⁻¹ := by
    calc (6 / 5 : ℝ) = (((6 / 5 : ℝ)) ^ 8) ^ ((8 : ℕ) : ℝ)⁻¹ :=
          (Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)).symm
      _ ≤ ((p : ℝ)) ^ ((8 : ℕ) : ℝ)⁻¹ := Real.rpow_le_rpow (by norm_num) hbase (by positivity)
  linarith

/-- Large primes contribute at most `q ^ (1/8)` to the local majorant. -/
private lemma localMajorant_large_part (q : ℕ) (hq : 0 < q) :
    ∏ p ∈ q.primeFactors.filter (fun p => ¬ p < 30), (1 + 6 / (p : ℝ)) ≤
      (q : ℝ) ^ ((8 : ℕ) : ℝ)⁻¹ := by
  have h1 : ∀ p ∈ q.primeFactors.filter (fun p => ¬ p < 30),
      1 + 6 / (p : ℝ) ≤ (p : ℝ) ^ ((8 : ℕ) : ℝ)⁻¹ := by
    intro p hp
    have h30 : 30 ≤ p := by
      have := (Finset.mem_filter.mp hp).2
      omega
    exact one_add_six_div_le_eighth h30
  have hstep : ∏ p ∈ q.primeFactors.filter (fun p => ¬ p < 30), (1 + 6 / (p : ℝ))
      ≤ ∏ p ∈ q.primeFactors.filter (fun p => ¬ p < 30), (p : ℝ) ^ ((8 : ℕ) : ℝ)⁻¹ :=
    prod_le_prod_nonneg (fun i hi => by positivity) h1
  calc ∏ p ∈ q.primeFactors.filter (fun p => ¬ p < 30), (1 + 6 / (p : ℝ))
      ≤ ∏ p ∈ q.primeFactors.filter (fun p => ¬ p < 30), (p : ℝ) ^ ((8 : ℕ) : ℝ)⁻¹ := hstep
    _ = (∏ p ∈ q.primeFactors.filter (fun p => ¬ p < 30), (p : ℝ)) ^ ((8 : ℕ) : ℝ)⁻¹ :=
        Real.finsetProd_rpow _ _ (fun p hp => by positivity) _
    _ ≤ (∏ p ∈ q.primeFactors, (p : ℝ)) ^ ((8 : ℕ) : ℝ)⁻¹ := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        apply prod_le_prod_of_subset_nonneg (Finset.filter_subset _ _)
        · intro i hi
          positivity
        · intro i hi _
          have h2 : 2 ≤ i := (Nat.prime_of_mem_primeFactors hi).two_le
          exact_mod_cast (show (1 : ℕ) ≤ i by omega)
    _ ≤ (q : ℝ) ^ ((8 : ℕ) : ℝ)⁻¹ := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        have hd := Nat.prod_primeFactors_dvd q
        have hle : (∏ p ∈ q.primeFactors, p) ≤ q := Nat.le_of_dvd hq hd
        have hcast : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ) := by
          push_cast
          ring
        rw [← hcast]
        exact_mod_cast hle

/-- Page 14 display 47 growth: the local majorant is at most `7^10 q ^ (1/8)`. -/
private lemma localMajorant_le (q : ℕ) (hq : 0 < q) :
    (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) ≤ (7 : ℝ) ^ 10 * (q : ℝ) ^ ((8 : ℕ) : ℝ)⁻¹ := by
  have hsplit := Finset.prod_filter_mul_prod_filter_not (s := q.primeFactors) (p := fun p => p < 30)
    (f := fun p => 1 + 6 / (p : ℝ))
  rw [← hsplit]
  have hsp := localMajorant_small_part q
  have hlp := localMajorant_large_part q hq
  have hsp0 : (0 : ℝ) ≤ ∏ p ∈ q.primeFactors.filter (fun p => ¬ p < 30), (1 + 6 / (p : ℝ)) :=
    Finset.prod_nonneg (fun p hp => by positivity)
  have h7 : (0 : ℝ) ≤ (7 : ℝ) ^ 10 := by positivity
  exact mul_le_mul hsp hlp hsp0 h7

/-- LEAF. Page 15 third display, numerical part of the double sum.
The local products have arbitrarily small positive power growth by
page 14 display 47. Summing two such factors up to y to the one third
costs at most y to the three quarters. No A2, interval, or weight occurs. -/
private theorem majorant_pair_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ y P : ℝ, 1 ≤ y → 0 < P →
      (∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
        ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
          (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) * (∏ p ∈ r.primeFactors, (1 + 6 / (p : ℝ)))) ≤ C * y ^ (3 / 4 : ℝ) := by
  refine ⟨4 * (7 : ℝ) ^ 20, by positivity, ?_⟩
  intro y P hy hP
  set Z : ℕ := ⌊y ^ (1 / 3 : ℝ)⌋₊ with hZ
  set S : Finset ℕ := Finset.Ioc ⌊P⌋₊ Z with hS
  have hy1 : (0 : ℝ) < y := by linarith
  have hlM : ∀ q : ℕ, (0 : ℝ) ≤ (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) := by
    intro q
    exact Finset.prod_nonneg (fun p _ => by positivity)
  have hy13 : (1 : ℝ) ≤ y ^ (1 / 3 : ℝ) := by
    have h1 : (1 : ℝ) ≤ y := hy
    calc (1 : ℝ) = (1 : ℝ) ^ (1 / 3 : ℝ) := by simp
      _ ≤ y ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by norm_num) h1 (by norm_num)
  have hZle : (Z : ℝ) ≤ y ^ (1 / 3 : ℝ) := by
    have hfl := Nat.floor_le (show (0 : ℝ) ≤ y ^ (1 / 3 : ℝ) by positivity)
    rwa [← hZ] at hfl
  have hbdd : ∀ q ∈ S, (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) ≤ (7 : ℝ) ^ 10 * y ^ (1 / 24 : ℝ) := by
    intro q hq
    have hqmem := (hS ▸ hq : q ∈ Finset.Ioc ⌊P⌋₊ Z)
    have hq0 : 0 < q := by
      have := (Finset.mem_Ioc.mp hqmem).1
      omega
    have hqle : (q : ℝ) ≤ y ^ (1 / 3 : ℝ) := by
      have h2 : (q : ℝ) ≤ (Z : ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hqmem).2
      linarith
    calc (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) ≤ (7 : ℝ) ^ 10 * (q : ℝ) ^ ((8 : ℕ) : ℝ)⁻¹ := localMajorant_le q hq0
      _ ≤ (7 : ℝ) ^ 10 * (y ^ (1 / 3 : ℝ)) ^ ((8 : ℕ) : ℝ)⁻¹ := by
          have hr : (q : ℝ) ^ ((8 : ℕ) : ℝ)⁻¹ ≤ (y ^ (1 / 3 : ℝ)) ^ ((8 : ℕ) : ℝ)⁻¹ :=
            Real.rpow_le_rpow (by positivity) hqle (by positivity)
          nlinarith
      _ = (7 : ℝ) ^ 10 * y ^ ((1 / 3 : ℝ) * ((8 : ℕ) : ℝ)⁻¹) := by
          rw [Real.rpow_mul (le_of_lt hy1)]
      _ = (7 : ℝ) ^ 10 * y ^ (1 / 24 : ℝ) := by norm_num
  have hsum_le : (∑ q ∈ S, (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ)))) ≤
      2 * y ^ (1 / 3 : ℝ) * ((7 : ℝ) ^ 10 * y ^ (1 / 24 : ℝ)) := by
    have h1 : (∑ q ∈ S, (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ)))) ≤ (S.card : ℝ) * ((7 : ℝ) ^ 10 * y ^ (1 / 24 : ℝ)) := by
      have h := Finset.sum_le_card_nsmul S (fun q => (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))))
        ((7 : ℝ) ^ 10 * y ^ (1 / 24 : ℝ)) hbdd
      simpa [nsmul_eq_mul] using h
    have hcard : (S.card : ℝ) ≤ 2 * y ^ (1 / 3 : ℝ) := by
      have hsub : S ⊆ Finset.range (Z + 1) := by
        intro q hq
        have hq' := (hS ▸ hq : q ∈ Finset.Ioc ⌊P⌋₊ Z)
        simp only [Finset.mem_range]
        have := (Finset.mem_Ioc.mp hq').2
        omega
      have hc : S.card ≤ Z + 1 := by
        have := Finset.card_le_card hsub
        simpa using this
      have hc' : (S.card : ℝ) ≤ (Z : ℝ) + 1 := by exact_mod_cast hc
      nlinarith
    have hnn : (0 : ℝ) ≤ (7 : ℝ) ^ 10 * y ^ (1 / 24 : ℝ) := by positivity
    nlinarith
  have hdouble : (∑ q ∈ S, ∑ r ∈ S.erase q, (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) * (∏ p ∈ r.primeFactors, (1 + 6 / (p : ℝ))))
      ≤ (∑ q ∈ S, (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ)))) * (∑ r ∈ S, (∏ p ∈ r.primeFactors, (1 + 6 / (p : ℝ)))) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro q hq
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset q S)
      (fun r hr _ => mul_nonneg (hlM q) (hlM r))
  have hyadd : y ^ (1 / 3 : ℝ) * y ^ (1 / 24 : ℝ) = y ^ (3 / 8 : ℝ) := by
    rw [← Real.rpow_add hy1]
    norm_num
  calc (∑ q ∈ S, ∑ r ∈ S.erase q, (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) * (∏ p ∈ r.primeFactors, (1 + 6 / (p : ℝ))))
      ≤ (∑ q ∈ S, (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ)))) * (∑ r ∈ S, (∏ p ∈ r.primeFactors, (1 + 6 / (p : ℝ)))) := hdouble
    _ ≤ (2 * y ^ (1 / 3 : ℝ) * ((7 : ℝ) ^ 10 * y ^ (1 / 24 : ℝ))) *
          (2 * y ^ (1 / 3 : ℝ) * ((7 : ℝ) ^ 10 * y ^ (1 / 24 : ℝ))) := by
        have hsum0 : (0 : ℝ) ≤ ∑ q ∈ S, (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) :=
          Finset.sum_nonneg (fun q _ => hlM q)
        have hup : (0 : ℝ) ≤ 2 * y ^ (1 / 3 : ℝ) * ((7 : ℝ) ^ 10 * y ^ (1 / 24 : ℝ)) := by positivity
        exact mul_le_mul hsum_le hsum_le hsum0 hup
    _ = (2 * (7 : ℝ) ^ 10 * (y ^ (1 / 3 : ℝ) * y ^ (1 / 24 : ℝ))) *
          (2 * (7 : ℝ) ^ 10 * (y ^ (1 / 3 : ℝ) * y ^ (1 / 24 : ℝ))) := by ring
    _ = (2 * (7 : ℝ) ^ 10 * y ^ (3 / 8 : ℝ)) * (2 * (7 : ℝ) ^ 10 * y ^ (3 / 8 : ℝ)) := by
        rw [hyadd]
    _ = 4 * (7 : ℝ) ^ 20 * (y ^ (3 / 8 : ℝ) * y ^ (3 / 8 : ℝ)) := by ring
    _ = 4 * (7 : ℝ) ^ 20 * y ^ (3 / 4 : ℝ) := by
        rw [← Real.rpow_add hy1]
        norm_num

/-- Page 15 second display. Weights constant in n have norm at most one.
CONDITIONAL on A2_conj and A2_coprime_mul. -/
private theorem weighted_pair_interval {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hqr : q ≠ r) (x y Q : ℝ) :
    (∑ n ∈ intervalNumbers x y,
      ((-(smoothWeight q Q : ℂ) * U1534.A2 n q) *
        (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * U1534.A2 n r)).re) ≤
      2 * ((∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) * (∏ p ∈ r.primeFactors, (1 + 6 / (p : ℝ)))) := by
  let u : ℂ := -(smoothWeight q Q : ℂ)
  let v : ℂ := -(smoothWeight r Q : ℂ)
  have hu : ‖u‖ ≤ 1 := by simpa [u] using smoothWeight_norm_le_one q Q
  have hv : ‖v‖ ≤ 1 := by simpa [v] using smoothWeight_norm_le_one r Q
  have huv : ‖u * (starRingEnd ℂ) v‖ ≤ 1 := by
    rw [norm_mul, norm_conj]
    exact mul_le_one₀ hu (norm_nonneg _) hv
  have heq : (∑ n ∈ intervalNumbers x y,
      ((u * U1534.A2 n q) * (starRingEnd ℂ) (v * U1534.A2 n r)).re) =
      ((u * (starRingEnd ℂ) v) * (∑ n ∈ intervalNumbers x y,
        U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r))).re := by
    rw [← Complex.re_sum, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [map_mul]
    ring
  change (∑ n ∈ intervalNumbers x y,
      ((u * U1534.A2 n q) * (starRingEnd ℂ) (v * U1534.A2 n r)).re) ≤ _
  rw [heq]
  calc
    _ ≤ ‖(u * (starRingEnd ℂ) v) * (∑ n ∈ intervalNumbers x y,
        U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r))‖ := Complex.re_le_norm _
    _ ≤ ‖∑ n ∈ intervalNumbers x y,
        U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) huv
    _ ≤ 2 * ∑ n ∈ Finset.range (q * r),
        ‖U1534.A2 n q * (starRingEnd ℂ) (U1534.A2 n r)‖ := by
      simpa only [intervalNumbers, ← Finset.Ico_succ_succ_eq_Ioc] using
        A2_conjugate_interval_bound hq hr hqr (Order.succ ⌊x⌋₊) (Order.succ ⌊x + y⌋₊)
    _ ≤ _ := mul_le_mul_of_nonneg_left (complete_period_majorant hq hr) (by norm_num)

/-- LEAF. Page 15 first display, using the coefficient bound in display 47.
Only equal moduli occur in this diagonal sum. The smooth weights have
absolute value at most one. The coefficient summation remains OPEN. -/
theorem diagonal_bound :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → 1 ≤ y → y ≤ x → 0 < P →
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ‖-(smoothWeight q Q : ℂ) * U1534.A2 n q‖ ^ 2) ≤
        C * (y / P * Real.log x) := by
  obtain ⟨C, x0, hC, hx0, hb⟩ := localMajorant_log_bound
  refine ⟨4 * C, x0, by positivity, hx0, ?_⟩
  intro x y P Q hx hy hyx hP
  have hx2 : 2 ≤ x := hx0.trans hx
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hpoint (n q : ℕ) (hq : q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊) :
      ‖-(smoothWeight q Q : ℂ) * U1534.A2 n q‖ ^ 2 ≤
        C * Real.log x * (1 / (q : ℝ) ^ 2) := by
    have hqn : 0 < q := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hq).1
    have hqy : (q : ℝ) ≤ y ^ (1 / 3 : ℝ) :=
      (Nat.cast_le.mpr (Finset.mem_Ioc.mp hq).2).trans (Nat.floor_le (by positivity))
    have hqx : (q : ℝ) ≤ x ^ (1 / 3 : ℝ) := hqy.trans
      (Real.rpow_le_rpow (by linarith) hyx (by norm_num))
    have hcoef := coefficient_product_bound n q hqn
    have hprod := hb x q hx hqn hqx
    have hw : ‖-(smoothWeight q Q : ℂ) * U1534.A2 n q‖ ≤ ‖U1534.A2 n q‖ := by
      rw [norm_mul, norm_neg]
      exact mul_le_of_le_one_left (norm_nonneg _) (smoothWeight_norm_le_one q Q)
    calc
      _ ≤ ((∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) / (q : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hw.trans hcoef) 2
      _ = (∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) ^ 2 * (1 / (q : ℝ) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hprod (by positivity)
  calc
    _ ≤ ∑ _n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          C * Real.log x * (1 / (q : ℝ) ^ 2) := by
      exact Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun q hq => hpoint n q hq
    _ = ((intervalNumbers x y).card : ℝ) * (C * Real.log x *
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊, 1 / (q : ℝ) ^ 2) := by
      simp [Finset.mul_sum]
    _ ≤ (2 * y) * (C * Real.log x * (2 / P)) := by
      apply mul_le_mul
      · exact Task271a.interval_card_le (by linarith) hy
      · exact mul_le_mul_of_nonneg_left (reciprocal_square_tail P _ hP) (by positivity)
      · positivity
      · positivity
    _ = (4 * C) * (y / P * Real.log x) := by ring

/-- Page 15 after the third display. A fixed positive power of y absorbs
any fixed logarithmic loss when y is at least x to a positive epsilon. -/
theorem quarter_power_absorption (A ε : ℝ) (hε : 0 < ε) :
    ∃ x0 : ℝ, 2 ≤ x0 ∧ ∀ x y : ℝ, x0 ≤ x → x ^ ε ≤ y →
      y ^ (3 / 4 : ℝ) ≤ y / Real.log x ^ A := by
  obtain ⟨x0, hb⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop A (show 0 < ε / 4 by linarith)).bound zero_lt_one)
  refine ⟨max x0 2, le_max_right _ _, ?_⟩
  intro x y hx hy
  have hx2 : 2 ≤ x := (le_max_right _ _).trans hx
  have hxp : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hyp : 0 < y := (Real.rpow_pos_of_pos hxp ε).trans_le hy
  have hl : Real.log x ^ A ≤ x ^ (ε / 4) := by
    have h := hb x ((le_max_left _ _).trans hx)
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hlog A),
      abs_of_pos (Real.rpow_pos_of_pos hxp (ε / 4)), one_mul] using h
  have hp : x ^ (ε / 4) ≤ y ^ (1 / 4 : ℝ) := by
    calc
      _ = (x ^ ε) ^ (1 / 4 : ℝ) := by rw [← Real.rpow_mul hxp.le]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hxp.le _) hy (by norm_num)
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hlog A)]
  calc
    _ ≤ y ^ (3 / 4 : ℝ) * y ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left (hl.trans hp) (Real.rpow_nonneg hyp.le _)
    _ = y := by rw [← Real.rpow_add hyp]; norm_num

/-- LEAF. Page 15 second and third displays in the proof of display 51.
Only distinct moduli occur. Display 47 and the incomplete period estimate
give a uniform y to the three quarters bound. This analytic summation
remains OPEN. The fixed constant absorbs the ordered pair factor two. -/
theorem off_diagonal_power_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x y P Q : ℝ,
      0 ≤ x → 1 ≤ y → 0 < P →
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
            ((-(smoothWeight q Q : ℂ) * U1534.A2 n q) *
              (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * U1534.A2 n r)).re) ≤
        C * y ^ (3 / 4 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := majorant_pair_sum
  refine ⟨2 * C, by positivity, ?_⟩
  intro x y P Q hx hy hP
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext q; rw [Finset.sum_comm]
  calc
    _ ≤ ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
        ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
          2 * ((∏ p ∈ q.primeFactors, (1 + 6 / (p : ℝ))) * (∏ p ∈ r.primeFactors, (1 + 6 / (p : ℝ)))) := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      have hqn : 0 < q := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hq).1
      have hrn : 0 < r := lt_of_le_of_lt (Nat.zero_le _)
        (Finset.mem_Ioc.mp (Finset.mem_of_mem_erase hr)).1
      exact weighted_pair_interval hqn hrn (Finset.ne_of_mem_erase hr).symm x y Q
    _ ≤ (2 * C) * y ^ (3 / 4 : ℝ) := by
      simp only [← Finset.mul_sum]
      have h := hb y P hy hP
      simp only [← Finset.mul_sum] at h
      nlinarith [h]

/-- Page 15 third display. The off diagonal logarithmic estimate follows
from the power saving leaf and elementary absorption.
CONDITIONAL on off_diagonal_power_bound. -/
theorem off_diagonal_bound (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
            ( (-(smoothWeight q Q : ℂ) * U1534.A2 n q) *
              (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * U1534.A2 n r)).re) ≤
        C * (y / Real.log x ^ A) := by
  obtain ⟨C, hC, hb⟩ := off_diagonal_power_bound
  obtain ⟨x0, hx0, ha⟩ := quarter_power_absorption A ε hε
  refine ⟨C, x0, hC, hx0, ?_⟩
  intro x y P Q hx hy _hyx hP _hPQ _hQ
  have hx2 : 2 ≤ x := hx0.trans hx
  have hy1 : 1 ≤ y := (Real.one_le_rpow (by linarith : 1 ≤ x) hε.le).trans hy
  exact (hb x y P Q (by linarith) hy1 hP).trans
    (mul_le_mul_of_nonneg_left (ha x y hx hy) hC.le)

/-- Pages 14 and 15 display 51. This is exactly tail_mean_square_input,
assembled from separate diagonal and off diagonal leaves.
CONDITIONAL on the two OPEN analytic leaves. -/
theorem tail_mean_square_from_parts (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y, ‖tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) ≤
        C * (y / P * Real.log x + y / Real.log x ^ A) := by
  obtain ⟨Cd, xd, hCd, hxd, hd⟩ := diagonal_bound
  obtain ⟨Co, xo, hCo, hxo, ho⟩ := off_diagonal_bound A ε hA hε
  refine ⟨Cd + Co, max xd xo, by positivity, hxd.trans (le_max_left _ _), ?_⟩
  intro x y P Q hx hy hyx hP hPQ hQ
  have hxd' : xd ≤ x := (le_max_left _ _).trans hx
  have hxo' : xo ≤ x := (le_max_right _ _).trans hx
  have hx2 : 2 ≤ x := hxd.trans hxd'
  have hy1 : 1 ≤ y := (Real.one_le_rpow (by linarith : 1 ≤ x) hε.le).trans hy
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hd' := hd x y P Q hxd' hy1 hyx hP
  have ho' := ho x y P Q hxo' hy hyx hP hPQ hQ
  have heq : (∑ n ∈ intervalNumbers x y, ‖tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) =
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ‖-(smoothWeight q Q : ℂ) * U1534.A2 n q‖ ^ 2) +
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
            ((-(smoothWeight q Q : ℂ) * U1534.A2 n q) *
              (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * U1534.A2 n r)).re) := by
    simp only [tail2, norm_sum_sq_split, Finset.sum_add_distrib]
  rw [heq]
  have hm : 0 ≤ y / P * Real.log x := by positivity
  have he : 0 ≤ y / Real.log x ^ A := by positivity
  calc
    _ ≤ Cd * (y / P * Real.log x) + Co * (y / Real.log x ^ A) := add_le_add hd' ho'
    _ ≤ (Cd + Co) * (y / P * Real.log x + y / Real.log x ^ A) := by nlinarith

/-- Page 14 display 49. Lemma 3.8 for j equals two follows from the
three new analytic leaves. This assembly does not invoke either old
truncation_input or old tail_mean_square_input.
CONDITIONAL on the three OPEN analytic leaves. -/
theorem lemma38_from_decomposed_leaves : lemma38_two := by
  intro A ε hA hε
  obtain ⟨Ce, Xe, hCe, hXe, he⟩ := Task271a.truncation_from_pointwise A ε hA hε
  obtain ⟨Ct, Xt, hCt, hXt, ht⟩ := tail_mean_square_from_parts A ε hA hε
  refine ⟨2 * (Ce + Ct), max Xe Xt, by positivity,
    le_trans hXe (le_max_left _ _), ?_⟩
  intro x y P Q hx hy hyx hP hPQ hQ
  have hxe : Xe ≤ x := le_trans (le_max_left _ _) hx
  have hxt : Xt ≤ x := le_trans (le_max_right _ _) hx
  have hx2 : 2 ≤ x := hXe.trans hxe
  have hxp : 0 < x := by linarith
  have hyp : 0 < y := lt_of_lt_of_le (Real.rpow_pos_of_pos hxp _) hy
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have he' := he x y P Q hxe hy hyx hP hPQ hQ
  have ht' := ht x y P Q hxt hy hyx hP hPQ hQ
  have hs := mean_square_add (intervalNumbers x y)
    (fun n => tail2 n P (y ^ (1 / 3 : ℝ)) Q)
    (fun n => (series2 n P - product2 n Q) - tail2 n P (y ^ (1 / 3 : ℝ)) Q)
  simp only [add_sub_cancel] at hs
  have hmain : 0 ≤ y / P * Real.log x := by positivity
  have herr : Ce * (y / Real.log x ^ A) ≤
      Ce * (y / P * Real.log x + y / Real.log x ^ A) := by
    nlinarith
  calc _ ≤ 2 * (∑ n ∈ intervalNumbers x y, ‖tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) +
      2 * (∑ n ∈ intervalNumbers x y,
        ‖(series2 n P - product2 n Q) - tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) := hs
    _ ≤ 2 * (Ct * (y / P * Real.log x + y / Real.log x ^ A)) +
      2 * (Ce * (y / Real.log x ^ A)) := by linarith
    _ ≤ 2 * (Ce + Ct) * (y / P * Real.log x + y / Real.log x ^ A) := by nlinarith

end LeanLab.KumchevLiu2007.Task271b

