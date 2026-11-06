/-
Chinese remainder supply for the three-square coefficient.
Source Schwarz Part I page 28 and Part II page 83 Lemma 2.4.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp403d

namespace LeanLab.KumchevLiu2007.Task438e

open Real Complex U1534 Task129c
open scoped BigOperators

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

/-- Schwarz Part I page 28. Transport one reduced residue sum through CRT. -/
private lemma unit_sum_crt (q r : ℕ) [NeZero q] [NeZero r] [NeZero (q * r)]
    (h : q.Coprime r) (G : ZMod (q * r) → ℂ) :
    (∑ a ∈ (Finset.univ : Finset (ZMod (q * r))).filter IsUnit, G a) =
      ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
        ∑ b ∈ (Finset.univ : Finset (ZMod r)).filter IsUnit,
          G ((ZMod.chineseRemainder h).symm (a, b)) := by
  classical
  have he : (∑ a ∈ (Finset.univ : Finset (ZMod (q * r))).filter IsUnit, G a) =
      ∑ p ∈ (Finset.univ : Finset (ZMod q × ZMod r)).filter IsUnit,
        G ((ZMod.chineseRemainder h).symm p) := by
    refine Finset.sum_bij (fun a _ => ZMod.chineseRemainder h a) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact ha.map (ZMod.chineseRemainder h).toMonoidHom
    · intro a ha b hb hab
      exact (ZMod.chineseRemainder h).injective hab
    · intro p hp
      refine ⟨(ZMod.chineseRemainder h).symm p, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp.map (ZMod.chineseRemainder h).symm.toMonoidHom
    · intro a ha
      simp
  rw [he]
  have hp : (Finset.univ : Finset (ZMod q × ZMod r)).filter IsUnit =
      ((Finset.univ : Finset (ZMod q)).filter IsUnit) ×ˢ
      ((Finset.univ : Finset (ZMod r)).filter IsUnit) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    exact Prod.isUnit_iff
  rw [hp, Finset.sum_product]

/-- Schwarz Part I page 28. The character of a CRT residue splits with Bezout twists. -/
private lemma char_crt (q r : ℕ) [NeZero q] [NeZero r] [NeZero (q * r)]
    (h : q.Coprime r) (a : ZMod q) (b : ZMod r) :
    ZMod.stdAddChar (N := q * r) ((ZMod.chineseRemainder h).symm (a, b)) =
      ZMod.stdAddChar (N := q) (a * (Nat.gcdB q r : ℤ)) *
      ZMod.stdAddChar (N := r) (b * (Nat.gcdA q r : ℤ)) := by
  rw [stdAddChar_crt_split' q r h]
  have h1 : (ZMod.cast ((ZMod.chineseRemainder h).symm (a, b)) : ZMod q) = a := by
    have hp := congrArg Prod.fst ((ZMod.chineseRemainder h).apply_symm_apply (a, b))
    simpa [ZMod.chineseRemainder, ZMod.castHom_apply] using hp
  have h2 : (ZMod.cast ((ZMod.chineseRemainder h).symm (a, b)) : ZMod r) = b := by
    have hp := congrArg Prod.snd ((ZMod.chineseRemainder h).apply_symm_apply (a, b))
    simpa [ZMod.chineseRemainder, ZMod.castHom_apply] using hp
  rw [h1, h2]

/-- Schwarz Part I page 28. A reduced quadratic sum splits into two twisted sums. -/
private lemma quadratic_sum_crt (q r : ℕ) [NeZero q] [NeZero r] [NeZero (q * r)]
    (h : q.Coprime r) (a : ZMod q) (b : ZMod r) :
    (∑ x ∈ (Finset.univ : Finset (ZMod (q * r))).filter IsUnit,
      ZMod.stdAddChar (N := q * r) ((ZMod.chineseRemainder h).symm (a, b) * x * x)) =
    (∑ x ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
      ZMod.stdAddChar (N := q) ((a * (Nat.gcdB q r : ℤ)) * x * x)) *
    (∑ x ∈ (Finset.univ : Finset (ZMod r)).filter IsUnit,
      ZMod.stdAddChar (N := r) ((b * (Nat.gcdA q r : ℤ)) * x * x)) := by
  classical
  rw [unit_sum_crt q r h, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  have he : (ZMod.chineseRemainder h).symm (a, b) *
      (ZMod.chineseRemainder h).symm (x, y) * (ZMod.chineseRemainder h).symm (x, y) =
      (ZMod.chineseRemainder h).symm (a * x * x, b * y * y) := by
    simp only [← map_mul, Prod.mk_mul_mk]
  rw [he, char_crt q r h]
  congr 2 <;> ring

/-- Schwarz Part I page 28. The linear phase splits with the same twists. -/
private lemma negative_char_crt (q r n : ℕ) [NeZero q] [NeZero r] [NeZero (q * r)]
    (h : q.Coprime r) (a : ZMod q) (b : ZMod r) :
    ZMod.stdAddChar (N := q * r)
      (-((ZMod.chineseRemainder h).symm (a, b) * (n : ZMod (q * r)))) =
      ZMod.stdAddChar (N := q) (-((a * (Nat.gcdB q r : ℤ)) * (n : ZMod q))) *
      ZMod.stdAddChar (N := r) (-((b * (Nat.gcdA q r : ℤ)) * (n : ZMod r))) := by
  have hn : (n : ZMod (q * r)) =
      (ZMod.chineseRemainder h).symm ((n : ZMod q), (n : ZMod r)) := by
    symm
    exact map_natCast (ZMod.chineseRemainder h).symm n
  rw [hn, ← map_mul, ← map_neg]
  change ZMod.stdAddChar ((ZMod.chineseRemainder h).symm
    (-(a * (n : ZMod q)), -(b * (n : ZMod r)))) = _
  rw [char_crt q r h]
  congr 2 <;> ring

/-- Schwarz Part I page 28 and Part II page 83. The unnormalised
three-square coefficient sum is multiplicative. -/
private lemma cubic_sum_crt (n q r : ℕ) [NeZero q] [NeZero r] [NeZero (q * r)]
    (h : q.Coprime r) :
    (∑ a ∈ (Finset.univ : Finset (ZMod (q * r))).filter IsUnit,
      (∑ x ∈ (Finset.univ : Finset (ZMod (q * r))).filter IsUnit,
        ZMod.stdAddChar (N := q * r) (a * x * x)) ^ 3 *
          ZMod.stdAddChar (N := q * r) (-(a * (n : ZMod (q * r))))) =
    (∑ a ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
      (∑ x ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
        ZMod.stdAddChar (N := q) (a * x * x)) ^ 3 *
          ZMod.stdAddChar (N := q) (-(a * (n : ZMod q)))) *
    (∑ a ∈ (Finset.univ : Finset (ZMod r)).filter IsUnit,
      (∑ x ∈ (Finset.univ : Finset (ZMod r)).filter IsUnit,
        ZMod.stdAddChar (N := r) (a * x * x)) ^ 3 *
          ZMod.stdAddChar (N := r) (-(a * (n : ZMod r)))) := by
  classical
  let F : ZMod q → ℂ := fun a =>
    (∑ x ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
      ZMod.stdAddChar (N := q) (a * x * x)) ^ 3 *
        ZMod.stdAddChar (N := q) (-(a * (n : ZMod q)))
  let G : ZMod r → ℂ := fun a =>
    (∑ x ∈ (Finset.univ : Finset (ZMod r)).filter IsUnit,
      ZMod.stdAddChar (N := r) (a * x * x)) ^ 3 *
        ZMod.stdAddChar (N := r) (-(a * (n : ZMod r)))
  rw [unit_sum_crt q r h]
  calc
    _ = ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
        ∑ b ∈ (Finset.univ : Finset (ZMod r)).filter IsUnit,
          F (a * (Nat.gcdB q r : ℤ)) * G (b * (Nat.gcdA q r : ℤ)) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [quadratic_sum_crt q r h, negative_char_crt q r n h, mul_pow]
      dsimp [F, G]
      ring
    _ = (∑ a ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
          F (a * (Nat.gcdB q r : ℤ))) *
        (∑ b ∈ (Finset.univ : Finset (ZMod r)).filter IsUnit,
          G (b * (Nat.gcdA q r : ℤ))) := by rw [Finset.sum_mul_sum]
    _ = _ := by
      rw [sum_units_mul_shift q _ (gcdB_isUnit q r h),
        sum_units_mul_shift r _ (gcdA_isUnit q r h)]

/-- Page 13 property i. Exact local coefficient supply from the written CRT proof
in Schwarz Part I page 28, cited by Part II page 83 Lemma 2.4. -/
theorem A3_coprime_mul (n a b : ℕ) (hab : a.Coprime b) :
    A3 n (a * b) = A3 n a * A3 n b := by
  classical
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [A3]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [A3]
  letI : NeZero a := ⟨ha.ne'⟩
  letI : NeZero b := ⟨hb.ne'⟩
  letI : NeZero (a * b) := ⟨Nat.mul_ne_zero ha.ne' hb.ne'⟩
  rw [Task342h.A3_zmod_formula, Task342h.A3_zmod_formula,
    Task342h.A3_zmod_formula, cubic_sum_crt n a b hab, Nat.totient_mul hab]
  push_cast
  ring

#print axioms stdAddChar_crt_split
#print axioms stdAddChar_crt_split'
#print axioms sum_units_mul_shift
#print axioms gcdB_isUnit
#print axioms gcdA_isUnit
#print axioms unit_sum_crt
#print axioms char_crt
#print axioms quadratic_sum_crt
#print axioms negative_char_crt
#print axioms cubic_sum_crt
#print axioms A3_coprime_mul

end LeanLab.KumchevLiu2007.Task438e
