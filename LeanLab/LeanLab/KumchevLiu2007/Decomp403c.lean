/-
The three-square case of Lemma 3.8 on pages 14 and 15.
The supply leaves truncation_input and diagonal_bound are PROVED here from the inlined
Task438 chain below, so lemma38_three has no sorry.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp403b
import LeanLab.PNTSieve.MertensUpper

namespace LeanLab.KumchevLiu2007.Task403c

open Real Complex Task129b Task129c
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Page 13 display 45. The truncated three-square singular series. -/
noncomputable def series3 (n : ℕ) (P : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, A3 n q

/-- Page 13 display 45 and property ii. The three-square singular product
has odd prime factors and a separate factor at 2 with powers through 8. -/
noncomputable def product3 (n : ℕ) (Q : ℝ) : ℂ :=
  (if 2 ≤ Q then 1 + A3 n 2 + A3 n 4 + A3 n 8 else 1) *
    ∏ p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter (fun p => p.Prime ∧ 2 < p),
      (1 + A3 n p)

/-- Page 14 below display 50. Direct subtraction gives the coefficient minus Psi.
This retains the corrected sign already used for the two-variable tail. -/
noncomputable def tail3 (n : ℕ) (P T Q : ℝ) : ℂ :=
  ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊T⌋₊, -(smoothWeight q Q : ℂ) * A3 n q

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
private theorem A3_coprime_mul (n a b : ℕ) (hab : a.Coprime b) :
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


/-- Schwarz page 82 Lemma 2.1, elementary translation proof.
A square zero residue h with 2h nonzero forces every unit frequency
reduced quadratic character sum to vanish. -/
private theorem quadratic_sum_zero_of_square_zero (q : ℕ) [NeZero q]
    (a h : ZMod q) (ha : IsUnit a) (hh : h ^ 2 = 0) (h2 : 2 * h ≠ 0) :
    (∑ x ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
      ZMod.stdAddChar (N := q) (a * x * x)) = 0 := by
  classical
  let U : Finset (ZMod q) := Finset.univ.filter IsUnit
  let f : ZMod q → ℂ := fun x => ZMod.stdAddChar (N := q) (a * x * x)
  have hnil (t : ZMod q) : IsNilpotent (t * h) := by
    refine ⟨2, ?_⟩
    rw [mul_pow, hh, mul_zero]
  have hshift (t : ZMod q) : (∑ x ∈ U, f (x + t * h)) = ∑ x ∈ U, f x := by
    refine Finset.sum_bij (fun x _ => x + t * h) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact (hnil t).isUnit_add_left_of_commute hx (Commute.all _ _)
    · intro x hx y hy hxy
      exact add_right_cancel hxy
    · intro x hx
      refine ⟨x + (-t) * h, ?_, by ring⟩
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact (hnil (-t)).isUnit_add_left_of_commute hx (Commute.all _ _)
    · intro x hx
      rfl
  have hinner (x : ZMod q) (hx : x ∈ U) : (∑ t : ZMod q, f (x + t * h)) = 0 := by
    have hxU : IsUnit x := (Finset.mem_filter.mp hx).2
    have hc : 2 * a * x * h ≠ 0 := by
      have he : 2 * a * x * h = (a * x) * (2 * h) := by ring
      rw [he]
      exact fun hz => h2 ((ha.mul hxU).mul_right_eq_zero.mp hz)
    have he (t : ZMod q) : f (x + t * h) =
        f x * ZMod.stdAddChar (N := q) (t * (2 * a * x * h)) := by
      have halg : a * (x + t * h) * (x + t * h) = a * x * x + t * (2 * a * x * h) := by
        have hsq : h * h = 0 := by simpa [sq] using hh
        linear_combination a * t ^ 2 * hsq
      dsimp [f]
      rw [halg, AddChar.map_add_eq_mul]
    simp_rw [he]
    rw [← Finset.mul_sum]
    have hs := AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := q))
      (2 * a * x * h) (ZMod.isPrimitive_stdAddChar q)
    simp only [ite_eq_right hc, Nat.cast_zero] at hs
    rw [hs, mul_zero]
  have he : (q : ℂ) * (∑ x ∈ U, f x) = 0 := by
    calc
      _ = ∑ t : ZMod q, ∑ x ∈ U, f (x + t * h) := by simp [hshift]
      _ = ∑ x ∈ U, ∑ t : ZMod q, f (x + t * h) := Finset.sum_comm
      _ = 0 := Finset.sum_eq_zero hinner
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  exact (mul_eq_zero.mp he).resolve_left hq0

/-- Schwarz page 82 Lemma 2.1. An admissible exponent d gives a square zero
translation modulo p to k and a nonzero doubled translation. -/
private theorem quadratic_sum_prime_power_zero (p k d : ℕ) [NeZero (p ^ k)] (hp : 0 < p)
    (hkd : k ≤ 2 * d) (hsmall : 0 < 2 * p ^ d) (hlarge : 2 * p ^ d < p ^ k)
    (a : ZMod (p ^ k)) (ha : IsUnit a) :
    (∑ x ∈ (Finset.univ : Finset (ZMod (p ^ k))).filter IsUnit,
      ZMod.stdAddChar (N := p ^ k) (a * x * x)) = 0 := by
  classical
  apply quadratic_sum_zero_of_square_zero (p ^ k) a ((p ^ d : ℕ) : ZMod (p ^ k)) ha
  · have hd : p ^ k ∣ (p ^ d) ^ 2 := by
      rw [← pow_mul]
      exact pow_dvd_pow p (by omega)
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact hd
  · have hd : ¬ p ^ k ∣ 2 * p ^ d := Nat.not_dvd_of_pos_of_lt hsmall hlarge
    rw [show (2 : ZMod (p ^ k)) * ((p ^ d : ℕ) : ZMod (p ^ k)) =
      ((2 * p ^ d : ℕ) : ZMod (p ^ k)) by push_cast; rfl]
    exact fun hz => hd ((ZMod.natCast_eq_zero_iff _ _).mp hz)

/-- Page 13 property ii and Schwarz page 82 Lemma 2.1.
Every reduced quadratic sum at a unit frequency vanishes at an odd prime
power from exponent 2 and at a power of 2 from exponent 4. -/
private theorem gaussS_prime_power_vanish (p k a : ℕ) (hp : p.Prime)
    (hk : (p ≠ 2 ∧ 2 ≤ k) ∨ (p = 2 ∧ 4 ≤ k)) (ha : a.Coprime (p ^ k)) :
    U1534.gaussS (p ^ k) a = 0 := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hau : IsUnit (a : ZMod (p ^ k)) := (ZMod.isUnit_iff_coprime a (p ^ k)).mpr ha
  rw [Task342h.gaussS_zmod]
  rcases hk with ⟨hodd, hk⟩ | ⟨rfl, hk⟩
  · have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
    have hpk : p ^ k = p * p ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ']
    apply quadratic_sum_prime_power_zero p k (k - 1) hp.pos (by omega) (by positivity)
      (by rw [hpk]; exact Nat.mul_lt_mul_of_pos_right hp2 (by positivity)) _ hau
  · have hpk : 2 ^ k = 4 * 2 ^ (k - 2) := by
      conv_lhs => rw [show k = 2 + (k - 2) by omega, pow_add]
      norm_num
    apply quadratic_sum_prime_power_zero 2 k (k - 2) (by norm_num) (by omega) (by positivity)
      (by rw [hpk]; exact Nat.mul_lt_mul_of_pos_right (by norm_num) (by positivity)) _ hau

/-- Page 13 property ii. Exact prime power coefficient vanishing supply.
The vanishing reduced quadratic sum kills every term of the coefficient. -/
private theorem A3_prime_power_vanish (n p k : ℕ) (hp : p.Prime)
    (hk : (p ≠ 2 ∧ 2 ≤ k) ∨ (p = 2 ∧ 4 ≤ k)) :
    A3 n (p ^ k) = 0 := by
  unfold A3
  have hs : (∑ a ∈ (Finset.range (p ^ k)).filter (fun a => Nat.Coprime a (p ^ k)),
      U1534.gaussS (p ^ k) a ^ 3 * U1534.ee (-((a * n : ℕ) : ℝ) / ((p ^ k : ℕ) : ℝ))) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [gaussS_prime_power_vanish p k a hp hk (Finset.mem_filter.mp ha).2]
    simp
  rw [hs, mul_zero]


/-- Page 14 before display 47. This complex character is nontrivial and quadratic
at every odd prime. -/
private theorem quadraticC_properties (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) ≠ 1 ∧ (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))).IsQuadratic := by
  constructor
  · intro he
    apply quadraticChar_ne_one (F := ZMod p) (by simpa only [ZMod.ringChar_zmod_n] using hp)
    exact (MulChar.ringHomComp_eq_one_iff Int.cast_injective).mp he
  · exact (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)

/-- Page 14 before display 47. Quadratic root counting changes the full
quadratic phase sum into its Gauss sum at every nonzero frequency. -/
private theorem full_quadratic_sum (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a : ZMod p) (ha : a ≠ 0) :
    (∑ x : ZMod p, ZMod.stdAddChar (N := p) (a * x ^ 2)) =
      ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) a * gaussSum (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))) (ZMod.stdAddChar (N := p)) := by
  classical
  have hroot (y : ZMod p) :
      ((Finset.univ.filter (fun x : ZMod p => x ^ 2 = y)).card : ℂ) =
        ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) y + 1 := by
    have h := quadraticChar_card_sqrts (F := ZMod p) (by simpa only [ZMod.ringChar_zmod_n] using hp) y
    have hc := congrArg (fun z : ℤ => (z : ℂ)) h
    simpa [MulChar.ringHomComp_apply, Set.toFinset_ofPred, Int.cast_add] using hc
  have hf : (∑ x : ZMod p, ZMod.stdAddChar (N := p) (a * x ^ 2)) =
      ∑ y : ZMod p, (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) y + 1) * ZMod.stdAddChar (N := p) (a * y) := by
    rw [← Finset.sum_fiberwise Finset.univ (fun x : ZMod p => x ^ 2)]
    apply Finset.sum_congr rfl
    intro y hy
    calc
      _ = ∑ _x ∈ Finset.univ.filter (fun x : ZMod p => x ^ 2 = y),
          ZMod.stdAddChar (N := p) (a * y) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [(Finset.mem_filter.mp hx).2]
      _ = _ := by simp [hroot]
  rw [hf]
  simp_rw [add_mul, one_mul, Finset.sum_add_distrib]
  have hs : (∑ y : ZMod p, ZMod.stdAddChar (N := p) (a * y)) = 0 := by
    simpa only [mul_comm, ite_eq_right ha, Nat.cast_zero] using
      (AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := p)) a (ZMod.isPrimitive_stdAddChar p))
  rw [hs, add_zero]
  have hg := gaussSum_mulShift_eq (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))) (ZMod.stdAddChar (N := p)) (Units.mk0 a ha)
  rw [(quadraticC_properties p hp).2.inv] at hg
  exact hg

/-- Page 2 display 8 and page 14 before display 47. Removing the zero residue
subtracts one from the full quadratic Gauss sum. -/
private theorem reduced_quadratic_sum (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a : ZMod p) (ha : a ≠ 0) :
    (∑ x ∈ (Finset.univ : Finset (ZMod p)).filter IsUnit,
      ZMod.stdAddChar (N := p) (a * x * x)) =
      ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) a * gaussSum (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))) (ZMod.stdAddChar (N := p)) - 1 := by
  classical
  have hset : (Finset.univ : Finset (ZMod p)).filter IsUnit = Finset.univ.erase 0 := by
    ext x
    simp [isUnit_iff_ne_zero]
  rw [hset]
  have h := Finset.sum_erase_add (Finset.univ : Finset (ZMod p))
    (fun x => ZMod.stdAddChar (N := p) (a * x * x)) (Finset.mem_univ 0)
  simp only [mul_zero, AddChar.map_zero_eq_one] at h
  have hf := full_quadratic_sum p hp a ha
  simp only [sq, ← mul_assoc] at hf
  rw [hf] at h
  exact eq_sub_of_add_eq h

/-- Page 14 before display 47. The square of the quadratic Gauss sum is
p times the quadratic character at minus one. -/
private theorem quadratic_gauss_sq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    gaussSum (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))) (ZMod.stdAddChar (N := p)) ^ 2 =
      ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) (-1) * (p : ℂ) := by
  simpa using gaussSum_sq (quadraticC_properties p hp).1
    (quadraticC_properties p hp).2 (ZMod.isPrimitive_stdAddChar p)

/-- Page 14 Legendre notation. A nonzero quadratic character value has square one. -/
private theorem quadraticC_sq (p : ℕ) [Fact p.Prime] (a : ZMod p) (ha : a ≠ 0) :
    ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) a ^ 2 = 1 := by
  have h := quadraticChar_sq_one (F := ZMod p) ha
  change (((quadraticChar (ZMod p)) a : ℤ) : ℂ) ^ 2 = 1
  exact_mod_cast h

/-- Page 14 Legendre notation. Every complex quadratic character value has norm at most one. -/
private theorem quadraticC_norm_le (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    ‖((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) a‖ ≤ 1 := by
  by_cases ha : a = 0
  · subst a
    simp [MulChar.ringHomComp_apply]
  · have hs := congrArg norm (quadraticC_sq p a ha)
    rw [norm_pow, norm_one] at hs
    nlinarith [norm_nonneg (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) a)]

/-- Page 14 before display 47. The Gauss sum twisted by b equals the quadratic
character at b times the original Gauss sum, including the zero twist. -/
private theorem quadratic_gauss_shift (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (b : ZMod p) :
    gaussSum (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))) ((ZMod.stdAddChar (N := p)).mulShift b) =
      ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) b * gaussSum (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))) (ZMod.stdAddChar (N := p)) := by
  by_cases hb : b = 0
  · subst b
    have hz : (ZMod.stdAddChar (N := p)).mulShift 0 = 1 := by ext x; simp
    rw [hz, gaussSum_one_right (quadraticC_properties p hp).1]
    simp [MulChar.ringHomComp_apply]
  · have h := gaussSum_mulShift_eq (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))) (ZMod.stdAddChar (N := p)) (Units.mk0 b hb)
    simpa only [(quadraticC_properties p hp).2.inv, Units.val_mk0] using h

/-- Page 14 before display 47. The squared quadratic Gauss sum has norm p. -/
private theorem quadratic_gauss_sq_norm (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ‖gaussSum (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))) (ZMod.stdAddChar (N := p)) ^ 2‖ = (p : ℝ) := by
  rw [quadratic_gauss_sq p hp, norm_mul, Complex.norm_natCast]
  have hs := congrArg norm (quadraticC_sq p (-1) (by simp))
  rw [norm_pow, norm_one] at hs
  have h1 : ‖((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) (-1)‖ = 1 := by nlinarith [norm_nonneg (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) (-1))]
  rw [h1, one_mul]

/-- Page 14 before display 47. Cubing the reduced quadratic Gauss sum leaves
one twisted Gauss sum and one Ramanujan sum. This is a finite algebra identity. -/
private theorem A3_odd_prime_formula (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (n : ℕ) :
    A3 n p =
      (((gaussSum (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))) (ZMod.stdAddChar (N := p))) ^ 3 +
        3 * gaussSum (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))) (ZMod.stdAddChar (N := p))) *
          (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) (-(n : ZMod p)) * gaussSum (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))) (ZMod.stdAddChar (N := p))) -
        (3 * (gaussSum (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))) (ZMod.stdAddChar (N := p))) ^ 2 + 1) *
          (if (n : ZMod p) = 0 then (p : ℂ) - 1 else -1)) / ((p : ℂ) - 1) ^ 3 := by
  classical
  let S : Finset (ZMod p) := Finset.univ.erase 0
  let G := gaussSum (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))) (ZMod.stdAddChar (N := p))
  have hset : (Finset.univ : Finset (ZMod p)).filter IsUnit = S := by
    ext x
    simp [S, isUnit_iff_ne_zero]
  have hterm (a : ZMod p) (ha : a ∈ S) :
      (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) a * G - 1) ^ 3 * ZMod.stdAddChar (N := p) (-(a * (n : ZMod p))) =
        (G ^ 3 + 3 * G) * (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) a * ZMod.stdAddChar (N := p) (-(a * (n : ZMod p)))) -
          (3 * G ^ 2 + 1) * ZMod.stdAddChar (N := p) (-(a * (n : ZMod p))) := by
    have hs := quadraticC_sq p a (Finset.ne_of_mem_erase ha)
    have ht : ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) a ^ 3 = ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) a := by rw [pow_succ, hs, one_mul]
    ring_nf
    rw [hs, ht]
    ring
  have hT : (∑ a ∈ S, ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) a * ZMod.stdAddChar (N := p) (-(a * (n : ZMod p)))) =
      ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) (-(n : ZMod p)) * G := by
    have h0 : ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) (0 : ZMod p) = 0 := by
      simp [MulChar.ringHomComp_apply]
    have ht := Finset.sum_erase_add (Finset.univ : Finset (ZMod p))
      (fun a => ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) a * ZMod.stdAddChar (N := p) (a * (-(n : ZMod p))))
      (Finset.mem_univ 0)
    simp only [h0, zero_mul, add_zero] at ht
    have he : (∑ a : ZMod p, ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) a * ZMod.stdAddChar (N := p) (a * (-(n : ZMod p)))) =
        gaussSum (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))) ((ZMod.stdAddChar (N := p)).mulShift (-(n : ZMod p))) := by
      simp only [gaussSum, AddChar.mulShift_apply, mul_comm]
    simpa only [S, ← mul_neg, he, quadratic_gauss_shift p hp, G] using ht
  have hR : (∑ a ∈ S, ZMod.stdAddChar (N := p) (-(a * (n : ZMod p)))) =
      if (n : ZMod p) = 0 then (p : ℂ) - 1 else -1 := by
    have ht := Finset.sum_erase_add (Finset.univ : Finset (ZMod p))
      (fun a => ZMod.stdAddChar (N := p) (a * (-(n : ZMod p)))) (Finset.mem_univ 0)
    have hs := AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := p))
      (-(n : ZMod p)) (ZMod.isPrimitive_stdAddChar p)
    simp only [zero_mul, AddChar.map_zero_eq_one] at ht
    rw [hs] at ht
    by_cases hn : (n : ZMod p) = 0 <;> simp [hn, S] at ht ⊢ <;> linear_combination ht
  rw [Task342h.A3_zmod_formula, Nat.totient_prime (Fact.out : p.Prime), hset]
  have hpp : 1 ≤ p := (Fact.out : p.Prime).one_le
  rw [Nat.cast_sub hpp, Nat.cast_one]
  have hsum : (∑ a ∈ S,
      (∑ x ∈ (Finset.univ : Finset (ZMod p)).filter IsUnit,
        ZMod.stdAddChar (N := p) (a * x * x)) ^ 3 *
        ZMod.stdAddChar (N := p) (-(a * (n : ZMod p)))) =
      (G ^ 3 + 3 * G) * (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) (-(n : ZMod p)) * G) -
        (3 * G ^ 2 + 1) * (if (n : ZMod p) = 0 then (p : ℂ) - 1 else -1) := by
    calc
      _ = ∑ a ∈ S, ((G ^ 3 + 3 * G) *
          (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) a * ZMod.stdAddChar (N := p) (-(a * (n : ZMod p)))) -
          (3 * G ^ 2 + 1) * ZMod.stdAddChar (N := p) (-(a * (n : ZMod p)))) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [reduced_quadratic_sum p hp a (Finset.ne_of_mem_erase ha)]
        exact hterm a ha
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hT, hR]
  rw [hset] at hsum
  rw [hsum]
  dsimp [G]
  ring

/-- Page 14 display 47, sharp form. The explicit Gauss expression gives a local
odd prime bound with the leading constant three, which is attained exactly when
the prime divides `n`; the constant 24 covers the remaining case. -/
private theorem A3_odd_prime_sharp (n p : ℕ) (hp : p.Prime) (hodd : 2 < p) :
    ‖A3 n p‖ ≤ (3 * (p : ℝ) + 24) / (p : ℝ) ^ 2 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : (0 : ℝ) < p := by positivity
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hodd
  have hp2 : p ≠ 2 := by omega
  let G := gaussSum (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)))
    (ZMod.stdAddChar (N := p))
  have hG : ‖G ^ 2‖ = (p : ℝ) := quadratic_gauss_sq_norm p hp2
  have hthree : ‖3 * G ^ 2 + 1‖ ≤ 3 * (p : ℝ) + 1 := by
    calc
      _ ≤ ‖(3 : ℂ) * G ^ 2‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = _ := by rw [norm_mul, hG]; norm_num
  have hden : ‖((p : ℂ) - 1) ^ 3‖ = ((p : ℝ) - 1) ^ 3 := by
    rw [norm_pow]
    congr 1
    rw [← Complex.ofReal_natCast p, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [A3_odd_prime_formula p hp2 n, norm_div, hden]
  change ‖(G ^ 3 + 3 * G) * (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) (-(n : ZMod p)) * G) -
    (3 * G ^ 2 + 1) * (if (n : ZMod p) = 0 then (p : ℂ) - 1 else -1)‖ /
      ((p : ℝ) - 1) ^ 3 ≤ _
  by_cases hn : (n : ZMod p) = 0
  · have hz : (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))) (0 : ZMod p) = 0 := by
      simp [MulChar.ringHomComp_apply]
    simp only [hn, neg_zero, hz, zero_mul, mul_zero, zero_sub, norm_neg, ite_true]
    have hpnorm : ‖(p : ℂ) - 1‖ = (p : ℝ) - 1 := by
      rw [← Complex.ofReal_natCast p, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [norm_mul, hpnorm]
    apply (div_le_iff₀ (pow_pos (by linarith : 0 < (p : ℝ) - 1) 3)).mpr
    have hnumer : ‖3 * G ^ 2 + 1‖ * ((p : ℝ) - 1) ≤
        (3 * (p : ℝ) + 1) * ((p : ℝ) - 1) :=
      mul_le_mul_of_nonneg_right hthree (by linarith)
    have hnum : ((3 : ℝ) * p + 1) * ((p : ℝ) - 1) ≤
        (3 * (p : ℝ) + 24) / (p : ℝ) ^ 2 * ((p : ℝ) - 1) ^ 3 := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < (p : ℝ) ^ 2)).mpr
      have hfac : (17 * (p : ℝ) ^ 2 - 45 * (p : ℝ) + 24)
          = ((p : ℝ) - 3) * (17 * (p : ℝ) + 6) + 42 := by ring
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (p : ℝ) - 3)
        (by linarith : (0 : ℝ) ≤ 17 * (p : ℝ) + 6), hfac,
        mul_pos (by linarith : (0 : ℝ) < (p : ℝ) - 1) (by linarith : (0 : ℝ) < (p : ℝ) - 1)]
    exact hnumer.trans hnum
  · rw [ite_eq_right hn]
    have heq : (G ^ 3 + 3 * G) * (((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) (-(n : ZMod p)) * G) -
        (3 * G ^ 2 + 1) * (-1) =
          ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) (-(n : ZMod p)) * G ^ 2 * (G ^ 2 + 3) + (3 * G ^ 2 + 1) := by ring
    rw [heq]
    have hnumer : ‖((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) (-(n : ZMod p)) * G ^ 2 * (G ^ 2 + 3) + (3 * G ^ 2 + 1)‖ ≤
        (p : ℝ) ^ 2 + 6 * (p : ℝ) + 1 := by
      have hplus : ‖G ^ 2 + 3‖ ≤ (p : ℝ) + 3 := by
        calc _ ≤ ‖G ^ 2‖ + ‖(3 : ℂ)‖ := norm_add_le _ _
             _ = _ := by rw [hG]; norm_num
      calc
        _ ≤ ‖((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)) (-(n : ZMod p)) * G ^ 2 * (G ^ 2 + 3)‖ + ‖3 * G ^ 2 + 1‖ := norm_add_le _ _
        _ ≤ (p : ℝ) * ((p : ℝ) + 3) + (3 * (p : ℝ) + 1) := by
          apply add_le_add _ hthree
          rw [norm_mul, norm_mul, hG]
          have hχ := quadraticC_norm_le p (-(n : ZMod p))
          exact mul_le_mul (mul_le_of_le_one_left hp0.le hχ) hplus
            (norm_nonneg _) hp0.le
        _ = _ := by ring
    apply (div_le_iff₀ (pow_pos (by linarith : 0 < (p : ℝ) - 1) 3)).mpr
    apply hnumer.trans
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (p : ℝ) ^ 2)).mpr
    have hcube : (0 : ℝ) ≤ 2 * (p : ℝ) ^ 3 + 15 * (p : ℝ) ^ 2 - 19 * (p : ℝ) + 12 := by
      nlinarith [sq_nonneg ((p : ℝ) - 3), hp3,
        mul_nonneg (by linarith : (0 : ℝ) ≤ (p : ℝ) - 3) (sq_nonneg (p : ℝ))]
    have hfac : (3 * (p : ℝ) + 24) * ((p : ℝ) - 1) ^ 3
          - (p : ℝ) ^ 2 * ((p : ℝ) ^ 2 + 6 * (p : ℝ) + 1)
        = ((p : ℝ) - 3) * (2 * (p : ℝ) ^ 3 + 15 * (p : ℝ) ^ 2 - 19 * (p : ℝ) + 12) + 12 := by
      ring
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (p : ℝ) - 3) hcube, hfac]

/-! ### Display 47 for the three-square coefficient -/

/-- Every exponential carries unit modulus. -/
private lemma norm_ee_403c (x : ℝ) : ‖U1534.ee x‖ = 1 := by
  unfold U1534.ee
  rw [Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

/-- The semigroup of units modulo `q` has totient many elements. -/
private lemma card_units_range (q : ℕ) :
    ((Finset.range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext a
  simp [Nat.coprime_comm]

/-- The Gauss sum of eq. (8) is at most the totient. -/
private lemma gaussS_norm_le_totient (q a : ℕ) : ‖U1534.gaussS q a‖ ≤ (q.totient : ℝ) := by
  unfold U1534.gaussS
  calc ‖∑ x ∈ (Finset.range q).filter (fun x => Nat.Coprime x q),
        U1534.ee ((a * x ^ 2 : ℕ) / (q : ℝ))‖
      ≤ ∑ x ∈ (Finset.range q).filter (fun x => Nat.Coprime x q),
        ‖U1534.ee ((a * x ^ 2 : ℕ) / (q : ℝ))‖ := norm_sum_le _ _
    _ = ∑ _x ∈ (Finset.range q).filter (fun x => Nat.Coprime x q), (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [norm_ee_403c]
    _ = (q.totient : ℝ) := by simp [card_units_range]

/-- Trivial size bound on the three-square coefficient. -/
private lemma A3_norm_le_totient (n q : ℕ) : ‖A3 n q‖ ≤ (q.totient : ℝ) := by
  unfold A3
  have hφ : (0 : ℝ) ≤ (q.totient : ℝ) := Nat.cast_nonneg _
  have hterm : ∀ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      ‖U1534.gaussS q a ^ 3 * U1534.ee (-((a * n : ℕ) : ℝ) / q)‖ ≤ (q.totient : ℝ) ^ 3 := by
    intro a _
    have h1 : ‖U1534.gaussS q a‖ ≤ (q.totient : ℝ) := gaussS_norm_le_totient q a
    rw [norm_mul, norm_pow, norm_ee_403c, mul_one]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 3
  have hcard := card_units_range q
  have hsum : ‖∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      U1534.gaussS q a ^ 3 * U1534.ee (-((a * n : ℕ) : ℝ) / q)‖ ≤ (q.totient : ℝ) ^ 4 := by
    calc ‖∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          U1534.gaussS q a ^ 3 * U1534.ee (-((a * n : ℕ) : ℝ) / q)‖
        ≤ ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          ‖U1534.gaussS q a ^ 3 * U1534.ee (-((a * n : ℕ) : ℝ) / q)‖ := norm_sum_le _ _
      _ ≤ ∑ _a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (q.totient : ℝ) ^ 3 :=
          Finset.sum_le_sum hterm
      _ = (((Finset.range q).filter (fun a => Nat.Coprime a q)).card : ℝ) * (q.totient : ℝ) ^ 3 := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ = (q.totient : ℝ) ^ 4 := by
          rw [hcard]
          ring
  have hnorm : ‖(1 / ((Nat.totient q : ℂ) ^ 3))‖ = 1 / (q.totient : ℝ) ^ 3 := by
    rw [one_div, norm_inv, norm_pow, Complex.norm_natCast, one_div]
  calc ‖1 / ((Nat.totient q : ℂ) ^ 3) *
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          U1534.gaussS q a ^ 3 * U1534.ee (-((a * n : ℕ) : ℝ) / q)‖
      = ‖(1 / ((Nat.totient q : ℂ) ^ 3))‖ *
        ‖∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          U1534.gaussS q a ^ 3 * U1534.ee (-((a * n : ℕ) : ℝ) / q)‖ := norm_mul _ _
    _ = (1 / (q.totient : ℝ) ^ 3) *
        ‖∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          U1534.gaussS q a ^ 3 * U1534.ee (-((a * n : ℕ) : ℝ) / q)‖ := by rw [hnorm]
    _ ≤ (1 / (q.totient : ℝ) ^ 3) * (q.totient : ℝ) ^ 4 := by
        apply mul_le_mul_of_nonneg_left hsum
        positivity
    _ = (q.totient : ℝ) := by
        rcases eq_or_lt_of_le hφ with h | h
        · rw [← h]; norm_num
        · field_simp

/-- `A3 n 1 = 1`. -/
private lemma A3_one_403c (n : ℕ) : A3 n 1 = 1 := by
  simp [A3, U1534.gaussS, U1534.ee]

/-- Page 14 display 47. The local majorant, written out; the even prime carries
the powers through eight and every odd prime has the sharp local constant. -/
private theorem A3_coefficient_bound (n : ℕ) :
    ∀ q : ℕ, 0 < q →
      ‖A3 n q‖ ≤
        (∏ p ∈ q.primeFactors, (if p = 2 then (45 : ℝ) else 3 + 24 / (p : ℝ))) / (q : ℝ) := by
  intro q
  induction q using Nat.recOnPrimeCoprime with
  | zero => intro h; omega
  | prime_pow p k hp =>
      intro hq
      by_cases hk : k = 0
      · subst hk
        rw [pow_zero]
        simp [A3_one_403c n]
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        rw [Nat.primeFactors_prime_pow hk hp, Finset.prod_singleton]
        by_cases htwo : p = 2
        · subst htwo
          by_cases hsmall : k ≤ 3
          · have h1 : ‖A3 n (2 ^ k)‖ ≤ ((2 ^ k).totient : ℝ) := A3_norm_le_totient n (2 ^ k)
            have hp2' : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
              conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
              ring
            have hcast : (((2 ^ k : ℕ) : ℝ)) = (2 : ℝ) ^ k := by push_cast; ring
            have hcast2 : (((2 ^ (k - 1) : ℕ) : ℝ)) = (2 : ℝ) ^ (k - 1) := by push_cast; ring
            have h2 : ((2 ^ k).totient : ℝ) = ((2 : ℝ) ^ (k - 1)) := by
              rw [Nat.totient_prime_pow hp hkpos]
              push_cast
              ring
            have hx : (2 : ℝ) ^ (k - 1) ≤ 4 := by
              calc (2 : ℝ) ^ (k - 1) ≤ (2 : ℝ) ^ (2 : ℕ) :=
                    pow_le_pow_right₀ (by norm_num) (by omega)
                _ = 4 := by norm_num
            have hx0 : (0 : ℝ) ≤ (2 : ℝ) ^ (k - 1) := by positivity
            have h3 : ((2 : ℝ) ^ (k - 1)) ≤ 45 / (2 * 2 ^ (k - 1)) := by
              rw [le_div_iff₀ (by positivity)]
              nlinarith [hx, hx0]
            rw [h2] at h1
            rw [hcast, hp2']
            simp only [if_true]
            linarith
          · push_neg at hsmall
            rw [A3_prime_power_vanish n 2 k hp (Or.inr ⟨rfl, by omega⟩), norm_zero]
            simp only [if_true]
            positivity
        · have hpodd : 2 < p := by
            have := hp.two_le
            omega
          by_cases hk1 : k = 1
          · subst hk1
            rw [pow_one, if_neg (by omega : ¬ p = 2)]
            have hS := A3_odd_prime_sharp n p hp hpodd
            have hp0 : (p : ℝ) ≠ 0 := by positivity
            calc ‖A3 n p‖ ≤ (3 * (p : ℝ) + 24) / (p : ℝ) ^ 2 := hS
              _ = (3 + 24 / (p : ℝ)) / (p : ℝ) := by field_simp
          · rw [A3_prime_power_vanish n p k hp (Or.inl ⟨htwo, by omega⟩), norm_zero]
            rw [if_neg (by omega : ¬ p = 2)]
            positivity
  | coprime a b ha hb hab ih_a ih_b =>
      intro hq
      have ha0 : a ≠ 0 := by omega
      have hb0 : b ≠ 0 := by omega
      have hdis := hab.disjoint_primeFactors
      have hM : (∏ p ∈ (a * b).primeFactors, (if p = 2 then (45 : ℝ) else 3 + 24 / (p : ℝ)))
          = (∏ p ∈ a.primeFactors, (if p = 2 then (45 : ℝ) else 3 + 24 / (p : ℝ))) *
            (∏ p ∈ b.primeFactors, (if p = 2 then (45 : ℝ) else 3 + 24 / (p : ℝ))) := by
        rw [Nat.primeFactors_mul ha0 hb0, Finset.prod_union hdis]
      rw [A3_coprime_mul n a b hab, norm_mul, hM, Nat.cast_mul]
      have ha1 : 0 < a := by omega
      have hb1 : 0 < b := by omega
      calc _ ≤ ((∏ p ∈ a.primeFactors, (if p = 2 then (45 : ℝ) else 3 + 24 / (p : ℝ))) / (a : ℝ)) *
            ((∏ p ∈ b.primeFactors, (if p = 2 then (45 : ℝ) else 3 + 24 / (p : ℝ))) / (b : ℝ)) :=
            mul_le_mul (ih_a ha1) (ih_b hb1) (norm_nonneg _)
              (le_trans (norm_nonneg _) (ih_a ha1))
        _ = _ := by ring

/-- Page 14 display 47. The local majorant grows slower than any power of `q`. -/
private lemma majorant_power_bound :
    ∀ q : ℕ, 0 < q →
      (∏ p ∈ q.primeFactors, (if p = 2 then (45 : ℝ) else 3 + 24 / (p : ℝ))) ≤
        (45 : ℝ) ^ 65536 * (q : ℝ) ^ (1 / 8 : ℝ) := by
  classical
  intro q hq
  have hfac : ∀ p ∈ q.primeFactors,
      (if p = 2 then (45 : ℝ) else 3 + 24 / (p : ℝ)) ≤ 45 := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    have hp2' : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    split_ifs with h
    · norm_num
    · have : 24 / (p : ℝ) ≤ 42 := by
        rw [div_le_iff₀ hp0]
        nlinarith
      linarith
  have hnonneg : ∀ p ∈ q.primeFactors,
      (0 : ℝ) ≤ (if p = 2 then (45 : ℝ) else 3 + 24 / (p : ℝ)) := by
    intro p hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast (Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp))
    split_ifs <;> positivity
  have hS : (∏ p ∈ q.primeFactors.filter (fun p => p < 65536),
      (if p = 2 then (45 : ℝ) else 3 + 24 / (p : ℝ))) ≤ (45 : ℝ) ^ 65536 := by
    calc ∏ p ∈ q.primeFactors.filter (fun p => p < 65536),
          (if p = 2 then (45 : ℝ) else 3 + 24 / (p : ℝ))
        ≤ ∏ _p ∈ q.primeFactors.filter (fun p => p < 65536), (45 : ℝ) :=
          Finset.prod_le_prod₀
            (fun p hp => hnonneg p (Finset.mem_filter.mp hp).1)
            (fun p hp => hfac p (Finset.mem_filter.mp hp).1)
      _ = (45 : ℝ) ^ (q.primeFactors.filter (fun p => p < 65536)).card := Finset.prod_const _
      _ ≤ (45 : ℝ) ^ 65536 := by
          apply pow_le_pow_right₀ (by norm_num)
          have hsub : q.primeFactors.filter (fun p => p < 65536) ⊆ Finset.range 65536 := by
            intro p hp
            exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
          simpa using Finset.card_le_card hsub
  have hT : (∏ p ∈ q.primeFactors.filter (fun p => ¬ p < 65536),
      (if p = 2 then (45 : ℝ) else 3 + 24 / (p : ℝ))) ≤ (q : ℝ) ^ (1 / 8 : ℝ) := by
    have hbig : ∀ p ∈ q.primeFactors.filter (fun p => ¬ p < 65536),
        (if p = 2 then (45 : ℝ) else 3 + 24 / (p : ℝ)) ≤ (p : ℝ) ^ (1 / 8 : ℝ) := by
      intro p hp
      have hpge : 65536 ≤ p := by
        have := (Finset.mem_filter.mp hp).2
        omega
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
      have hbase : (4 : ℝ) ≤ (p : ℝ) ^ (1 / 8 : ℝ) := by
        have h1 : (65536 : ℝ) ^ (1 / 8 : ℝ) ≤ (p : ℝ) ^ (1 / 8 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hpge) (by norm_num)
        have h2 : (65536 : ℝ) ^ (1 / 8 : ℝ) = 4 := by
          have he : (65536 : ℝ) = 4 ^ (8 : ℕ) := by norm_num
          rw [he, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          norm_num
        linarith
      have hp2 : p ≠ 2 := by omega
      have hfour : 3 + 24 / (p : ℝ) ≤ 4 := by
        have h24 : 24 / (p : ℝ) ≤ 1 := by
          rw [div_le_one hp0]
          have : (24 : ℝ) ≤ (p : ℝ) := by
            have : (65536 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpge
            linarith
          linarith
        linarith
      simp only [hp2, if_false]
      linarith
    calc ∏ p ∈ q.primeFactors.filter (fun p => ¬ p < 65536),
          (if p = 2 then (45 : ℝ) else 3 + 24 / (p : ℝ))
        ≤ ∏ p ∈ q.primeFactors.filter (fun p => ¬ p < 65536), (p : ℝ) ^ (1 / 8 : ℝ) :=
          Finset.prod_le_prod₀
            (fun p hp => hnonneg p (Finset.mem_filter.mp hp).1) hbig
      _ = ((∏ p ∈ q.primeFactors.filter (fun p => ¬ p < 65536), (p : ℝ))) ^ (1 / 8 : ℝ) :=
          Real.finsetProd_rpow (q.primeFactors.filter (fun p => ¬ p < 65536))
            (fun p : ℕ => (p : ℝ)) (fun p _ => by positivity) (1 / 8 : ℝ)
      _ ≤ (q : ℝ) ^ (1 / 8 : ℝ) := by
          apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
          have hle : (∏ p ∈ q.primeFactors.filter (fun p => ¬ p < 65536), p) ≤ q := by
            refine Nat.le_of_dvd hq ?_
            exact (Finset.prod_dvd_prod_of_subset _ q.primeFactors (fun p => p)
              (Finset.filter_subset _ _)).trans (Nat.prod_primeFactors_dvd q)
          have hle' : ((∏ p ∈ q.primeFactors.filter (fun p => ¬ p < 65536), p : ℕ) : ℝ) ≤ (q : ℝ) :=
            by exact_mod_cast hle
          simpa using hle'
  rw [← Finset.prod_filter_mul_prod_filter_not q.primeFactors (fun p => p < 65536)]
  exact mul_le_mul hS hT (by positivity) (by positivity)


end LeanLab.KumchevLiu2007.Task403c

/-! Inlined from Decomp403d.lean, unchanged except for the namespace prefix. -/
/-
A concrete limit of transferring the A2 majorant to A3.
Source page 13 display 45 and page 14 display 47.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.KumchevLiu2007.Task403cI403d

open Real Complex U1534 Task129c Task292a
open scoped BigOperators

/-- Page 2 display 8. The triangle inequality bounds the reduced Gauss sum by the totient. -/
theorem gaussS_norm_le_totient (q a : ℕ) :
    ‖gaussS q a‖ ≤ (Nat.totient q : ℝ) := by
  have hee (t : ℝ) : ‖ee t‖ = 1 := by simp [ee, Complex.norm_exp]
  unfold gaussS
  calc
    _ ≤ ∑ x ∈ (Finset.range q).filter (fun x => Nat.Coprime x q), (1 : ℝ) := by
      apply norm_sum_le_of_le
      intro x hx
      exact (hee _).le
    _ = _ := by simp [Nat.totient_eq_card_coprime, Nat.coprime_comm]

/-- Page 13 display 45. Applying the triangle inequality gives a coarse bound by the totient. -/
theorem A3_norm_le_totient (n q : ℕ) : ‖A3 n q‖ ≤ (Nat.totient q : ℝ) := by
  by_cases hq : q = 0
  · subst q
    simp [A3]
  have hphi : 0 < (Nat.totient q : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq))
  have hee (t : ℝ) : ‖ee t‖ = 1 := by simp [ee, Complex.norm_exp]
  have hb : ‖∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      gaussS q a ^ 3 * ee (-((a * n : ℕ) : ℝ) / q)‖ ≤ (Nat.totient q : ℝ) ^ 4 := by
    calc
      _ ≤ ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          (Nat.totient q : ℝ) ^ 3 := by
        apply norm_sum_le_of_le
        intro a ha
        rw [norm_mul, norm_pow, hee, mul_one]
        exact pow_le_pow_left₀ (norm_nonneg _) (gaussS_norm_le_totient q a) 3
      _ = _ := by
        simp [Nat.totient_eq_card_coprime, Nat.coprime_comm]
        ring
  unfold A3
  rw [norm_mul, norm_div, norm_one, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ 1 / (Nat.totient q : ℝ) ^ 3 * (Nat.totient q : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by field_simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Page 13 display 45. The admissible integer 507 has A3 at modulus 13
 equal to minus five eighteenths. This tests a proposed transfer of the lab A2 bound. -/
theorem A3_507_13 : InH3 507 ∧ A3 507 13 = -(5 / 18 : ℂ) := by
  constructor
  · norm_num [InH3]
  · letI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    have hc : (tripleRoots 13 507).card = 96 := by decide
    rw [A3_prime_count, hc]
    norm_num

/-- Page 14 display 47, a limitation of one lab majorant.
The exact A2 majorant with constant one fails for A3 even on H3. -/
theorem A2_majorant_not_valid_for_A3 :
    ¬ ∀ n q : ℕ, InH3 n → 0 < q → ‖A3 n q‖ ≤ localMajorant q / (q : ℝ) := by
  intro h
  have hb := h 507 13 A3_507_13.1 (by norm_num)
  have hm : localMajorant 13 = 19 / 13 := by
    norm_num [localMajorant, (show Nat.Prime 13 by norm_num).primeFactors]
  rw [A3_507_13.2, hm] at hb
  norm_num [norm_div] at hb

end LeanLab.KumchevLiu2007.Task403cI403d


/-! Inlined from Decomp438e.lean, unchanged except for the namespace prefix. -/
/-
Chinese remainder supply for the three-square coefficient.
Source Schwarz Part I page 28 and Part II page 83 Lemma 2.4.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.KumchevLiu2007.Task403cI438e

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


end LeanLab.KumchevLiu2007.Task403cI438e


/-! Inlined from Decomp438f.lean, unchanged except for the namespace prefix. -/
/-
Vanishing of reduced quadratic sums at higher prime powers.
Source page 13 property ii and Schwarz Part II page 82 Lemma 2.1.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.KumchevLiu2007.Task403cI438f

open Real Complex U1534 Task129c
open scoped BigOperators

/-- Schwarz page 82 Lemma 2.1, elementary translation proof.
A square zero residue h with 2h nonzero forces every unit frequency
reduced quadratic character sum to vanish. -/
theorem quadratic_sum_zero_of_square_zero (q : ℕ) [NeZero q]
    (a h : ZMod q) (ha : IsUnit a) (hh : h ^ 2 = 0) (h2 : 2 * h ≠ 0) :
    (∑ x ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
      ZMod.stdAddChar (N := q) (a * x * x)) = 0 := by
  classical
  let U : Finset (ZMod q) := Finset.univ.filter IsUnit
  let f : ZMod q → ℂ := fun x => ZMod.stdAddChar (N := q) (a * x * x)
  have hnil (t : ZMod q) : IsNilpotent (t * h) := by
    refine ⟨2, ?_⟩
    rw [mul_pow, hh, mul_zero]
  have hshift (t : ZMod q) : (∑ x ∈ U, f (x + t * h)) = ∑ x ∈ U, f x := by
    refine Finset.sum_bij (fun x _ => x + t * h) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact (hnil t).isUnit_add_left_of_commute hx (Commute.all _ _)
    · intro x hx y hy hxy
      exact add_right_cancel hxy
    · intro x hx
      refine ⟨x + (-t) * h, ?_, by ring⟩
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact (hnil (-t)).isUnit_add_left_of_commute hx (Commute.all _ _)
    · intro x hx
      rfl
  have hinner (x : ZMod q) (hx : x ∈ U) : (∑ t : ZMod q, f (x + t * h)) = 0 := by
    have hxU : IsUnit x := (Finset.mem_filter.mp hx).2
    have hc : 2 * a * x * h ≠ 0 := by
      have he : 2 * a * x * h = (a * x) * (2 * h) := by ring
      rw [he]
      exact fun hz => h2 ((ha.mul hxU).mul_right_eq_zero.mp hz)
    have he (t : ZMod q) : f (x + t * h) =
        f x * ZMod.stdAddChar (N := q) (t * (2 * a * x * h)) := by
      have halg : a * (x + t * h) * (x + t * h) = a * x * x + t * (2 * a * x * h) := by
        have hsq : h * h = 0 := by simpa [sq] using hh
        linear_combination a * t ^ 2 * hsq
      dsimp [f]
      rw [halg, AddChar.map_add_eq_mul]
    simp_rw [he]
    rw [← Finset.mul_sum]
    have hs := AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := q))
      (2 * a * x * h) (ZMod.isPrimitive_stdAddChar q)
    simp only [ite_eq_right hc, Nat.cast_zero] at hs
    rw [hs, mul_zero]
  have he : (q : ℂ) * (∑ x ∈ U, f x) = 0 := by
    calc
      _ = ∑ t : ZMod q, ∑ x ∈ U, f (x + t * h) := by simp [hshift]
      _ = ∑ x ∈ U, ∑ t : ZMod q, f (x + t * h) := Finset.sum_comm
      _ = 0 := Finset.sum_eq_zero hinner
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  exact (mul_eq_zero.mp he).resolve_left hq0

/-- Schwarz page 82 Lemma 2.1. An admissible exponent d gives a square zero
translation modulo p to k and a nonzero doubled translation. -/
theorem quadratic_sum_prime_power_zero (p k d : ℕ) [NeZero (p ^ k)] (hp : 0 < p)
    (hkd : k ≤ 2 * d) (hsmall : 0 < 2 * p ^ d) (hlarge : 2 * p ^ d < p ^ k)
    (a : ZMod (p ^ k)) (ha : IsUnit a) :
    (∑ x ∈ (Finset.univ : Finset (ZMod (p ^ k))).filter IsUnit,
      ZMod.stdAddChar (N := p ^ k) (a * x * x)) = 0 := by
  classical
  apply quadratic_sum_zero_of_square_zero (p ^ k) a ((p ^ d : ℕ) : ZMod (p ^ k)) ha
  · have hd : p ^ k ∣ (p ^ d) ^ 2 := by
      rw [← pow_mul]
      exact pow_dvd_pow p (by omega)
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact hd
  · have hd : ¬ p ^ k ∣ 2 * p ^ d := Nat.not_dvd_of_pos_of_lt hsmall hlarge
    rw [show (2 : ZMod (p ^ k)) * ((p ^ d : ℕ) : ZMod (p ^ k)) =
      ((2 * p ^ d : ℕ) : ZMod (p ^ k)) by push_cast; rfl]
    exact fun hz => hd ((ZMod.natCast_eq_zero_iff _ _).mp hz)

/-- Page 13 property ii and Schwarz page 82 Lemma 2.1.
Every reduced quadratic sum at a unit frequency vanishes at an odd prime
power from exponent 2 and at a power of 2 from exponent 4. -/
theorem gaussS_prime_power_vanish (p k a : ℕ) (hp : p.Prime)
    (hk : (p ≠ 2 ∧ 2 ≤ k) ∨ (p = 2 ∧ 4 ≤ k)) (ha : a.Coprime (p ^ k)) :
    gaussS (p ^ k) a = 0 := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hau : IsUnit (a : ZMod (p ^ k)) := (ZMod.isUnit_iff_coprime a (p ^ k)).mpr ha
  rw [Task342h.gaussS_zmod]
  rcases hk with ⟨hodd, hk⟩ | ⟨rfl, hk⟩
  · have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
    have hpk : p ^ k = p * p ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ']
    apply quadratic_sum_prime_power_zero p k (k - 1) hp.pos (by omega) (by positivity)
      (by rw [hpk]; exact Nat.mul_lt_mul_of_pos_right hp2 (by positivity)) _ hau
  · have hpk : 2 ^ k = 4 * 2 ^ (k - 2) := by
      conv_lhs => rw [show k = 2 + (k - 2) by omega, pow_add]
      norm_num
    apply quadratic_sum_prime_power_zero 2 k (k - 2) (by norm_num) (by omega) (by positivity)
      (by rw [hpk]; exact Nat.mul_lt_mul_of_pos_right (by norm_num) (by positivity)) _ hau

/-- Page 13 property ii. Exact prime power coefficient vanishing supply.
The vanishing reduced quadratic sum kills every term of the coefficient. -/
theorem A3_prime_power_vanish (n p k : ℕ) (hp : p.Prime)
    (hk : (p ≠ 2 ∧ 2 ≤ k) ∨ (p = 2 ∧ 4 ≤ k)) :
    A3 n (p ^ k) = 0 := by
  unfold A3
  have hs : (∑ a ∈ (Finset.range (p ^ k)).filter (fun a => Nat.Coprime a (p ^ k)),
      gaussS (p ^ k) a ^ 3 * ee (-((a * n : ℕ) : ℝ) / ((p ^ k : ℕ) : ℝ))) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [gaussS_prime_power_vanish p k a hp hk (Finset.mem_filter.mp ha).2]
    simp
  rw [hs, mul_zero]


end LeanLab.KumchevLiu2007.Task403cI438f


/-! Inlined from Decomp438g.lean, unchanged except for the namespace prefix. -/
/-
Odd prime coefficient estimate from quadratic characters.
Source page 14 before display 47 and Schwarz page 83 display 2.11.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.KumchevLiu2007.Task403cI438g

open Real Complex U1534 Task129c
open scoped BigOperators

/-- Page 14 Legendre symbol notation. The quadratic character with complex values. -/
noncomputable def quadraticC (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

/-- Page 14 before display 47. This complex character is nontrivial and quadratic
at every odd prime. -/
theorem quadraticC_properties (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    quadraticC p ≠ 1 ∧ (quadraticC p).IsQuadratic := by
  constructor
  · intro he
    apply quadraticChar_ne_one (F := ZMod p) (by simpa only [ZMod.ringChar_zmod_n] using hp)
    exact (MulChar.ringHomComp_eq_one_iff Int.cast_injective).mp he
  · exact (quadraticChar_isQuadratic (ZMod p)).comp (Int.castRingHom ℂ)

/-- Page 14 before display 47. Quadratic root counting changes the full
quadratic phase sum into its Gauss sum at every nonzero frequency. -/
theorem full_quadratic_sum (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a : ZMod p) (ha : a ≠ 0) :
    (∑ x : ZMod p, ZMod.stdAddChar (N := p) (a * x ^ 2)) =
      quadraticC p a * gaussSum (quadraticC p) (ZMod.stdAddChar (N := p)) := by
  classical
  have hroot (y : ZMod p) :
      ((Finset.univ.filter (fun x : ZMod p => x ^ 2 = y)).card : ℂ) =
        quadraticC p y + 1 := by
    have h := quadraticChar_card_sqrts (F := ZMod p) (by simpa only [ZMod.ringChar_zmod_n] using hp) y
    have hc := congrArg (fun z : ℤ => (z : ℂ)) h
    simpa [quadraticC, MulChar.ringHomComp_apply, Set.toFinset_ofPred, Int.cast_add] using hc
  have hf : (∑ x : ZMod p, ZMod.stdAddChar (N := p) (a * x ^ 2)) =
      ∑ y : ZMod p, (quadraticC p y + 1) * ZMod.stdAddChar (N := p) (a * y) := by
    rw [← Finset.sum_fiberwise Finset.univ (fun x : ZMod p => x ^ 2)]
    apply Finset.sum_congr rfl
    intro y hy
    calc
      _ = ∑ _x ∈ Finset.univ.filter (fun x : ZMod p => x ^ 2 = y),
          ZMod.stdAddChar (N := p) (a * y) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [(Finset.mem_filter.mp hx).2]
      _ = _ := by simp [hroot]
  rw [hf]
  simp_rw [add_mul, one_mul, Finset.sum_add_distrib]
  have hs : (∑ y : ZMod p, ZMod.stdAddChar (N := p) (a * y)) = 0 := by
    simpa only [mul_comm, ite_eq_right ha, Nat.cast_zero] using
      (AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := p)) a (ZMod.isPrimitive_stdAddChar p))
  rw [hs, add_zero]
  have hg := gaussSum_mulShift_eq (quadraticC p) (ZMod.stdAddChar (N := p)) (Units.mk0 a ha)
  rw [(quadraticC_properties p hp).2.inv] at hg
  exact hg

/-- Page 2 display 8 and page 14 before display 47. Removing the zero residue
subtracts one from the full quadratic Gauss sum. -/
theorem reduced_quadratic_sum (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (a : ZMod p) (ha : a ≠ 0) :
    (∑ x ∈ (Finset.univ : Finset (ZMod p)).filter IsUnit,
      ZMod.stdAddChar (N := p) (a * x * x)) =
      quadraticC p a * gaussSum (quadraticC p) (ZMod.stdAddChar (N := p)) - 1 := by
  classical
  have hset : (Finset.univ : Finset (ZMod p)).filter IsUnit = Finset.univ.erase 0 := by
    ext x
    simp [isUnit_iff_ne_zero]
  rw [hset]
  have h := Finset.sum_erase_add (Finset.univ : Finset (ZMod p))
    (fun x => ZMod.stdAddChar (N := p) (a * x * x)) (Finset.mem_univ 0)
  simp only [mul_zero, AddChar.map_zero_eq_one] at h
  have hf := full_quadratic_sum p hp a ha
  simp only [sq, ← mul_assoc] at hf
  rw [hf] at h
  exact eq_sub_of_add_eq h

/-- Page 14 before display 47. The square of the quadratic Gauss sum is
p times the quadratic character at minus one. -/
theorem quadratic_gauss_sq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    gaussSum (quadraticC p) (ZMod.stdAddChar (N := p)) ^ 2 =
      quadraticC p (-1) * (p : ℂ) := by
  simpa using gaussSum_sq (quadraticC_properties p hp).1
    (quadraticC_properties p hp).2 (ZMod.isPrimitive_stdAddChar p)

/-- Page 14 Legendre notation. A nonzero quadratic character value has square one. -/
theorem quadraticC_sq (p : ℕ) [Fact p.Prime] (a : ZMod p) (ha : a ≠ 0) :
    quadraticC p a ^ 2 = 1 := by
  have h := quadraticChar_sq_one (F := ZMod p) ha
  change (((quadraticChar (ZMod p)) a : ℤ) : ℂ) ^ 2 = 1
  exact_mod_cast h

/-- Page 14 Legendre notation. Every complex quadratic character value has norm at most one. -/
theorem quadraticC_norm_le (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    ‖quadraticC p a‖ ≤ 1 := by
  by_cases ha : a = 0
  · subst a
    simp [quadraticC, MulChar.ringHomComp_apply]
  · have hs := congrArg norm (quadraticC_sq p a ha)
    rw [norm_pow, norm_one] at hs
    nlinarith [norm_nonneg (quadraticC p a)]

/-- Page 14 before display 47. The Gauss sum twisted by b equals the quadratic
character at b times the original Gauss sum, including the zero twist. -/
theorem quadratic_gauss_shift (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (b : ZMod p) :
    gaussSum (quadraticC p) ((ZMod.stdAddChar (N := p)).mulShift b) =
      quadraticC p b * gaussSum (quadraticC p) (ZMod.stdAddChar (N := p)) := by
  by_cases hb : b = 0
  · subst b
    have hz : (ZMod.stdAddChar (N := p)).mulShift 0 = 1 := by ext x; simp
    rw [hz, gaussSum_one_right (quadraticC_properties p hp).1]
    simp [quadraticC, MulChar.ringHomComp_apply]
  · have h := gaussSum_mulShift_eq (quadraticC p) (ZMod.stdAddChar (N := p)) (Units.mk0 b hb)
    simpa only [(quadraticC_properties p hp).2.inv, Units.val_mk0] using h

/-- Page 14 before display 47. The squared quadratic Gauss sum has norm p. -/
theorem quadratic_gauss_sq_norm (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ‖gaussSum (quadraticC p) (ZMod.stdAddChar (N := p)) ^ 2‖ = (p : ℝ) := by
  rw [quadratic_gauss_sq p hp, norm_mul, Complex.norm_natCast]
  have hs := congrArg norm (quadraticC_sq p (-1) (by simp))
  rw [norm_pow, norm_one] at hs
  have h1 : ‖quadraticC p (-1)‖ = 1 := by nlinarith [norm_nonneg (quadraticC p (-1))]
  rw [h1, one_mul]

/-- Page 14 before display 47. Cubing the reduced quadratic Gauss sum leaves
one twisted Gauss sum and one Ramanujan sum. This is a finite algebra identity. -/
theorem A3_odd_prime_formula (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (n : ℕ) :
    A3 n p =
      (((gaussSum (quadraticC p) (ZMod.stdAddChar (N := p))) ^ 3 +
        3 * gaussSum (quadraticC p) (ZMod.stdAddChar (N := p))) *
          (quadraticC p (-(n : ZMod p)) * gaussSum (quadraticC p) (ZMod.stdAddChar (N := p))) -
        (3 * (gaussSum (quadraticC p) (ZMod.stdAddChar (N := p))) ^ 2 + 1) *
          (if (n : ZMod p) = 0 then (p : ℂ) - 1 else -1)) / ((p : ℂ) - 1) ^ 3 := by
  classical
  let S : Finset (ZMod p) := Finset.univ.erase 0
  let G := gaussSum (quadraticC p) (ZMod.stdAddChar (N := p))
  have hset : (Finset.univ : Finset (ZMod p)).filter IsUnit = S := by
    ext x
    simp [S, isUnit_iff_ne_zero]
  have hterm (a : ZMod p) (ha : a ∈ S) :
      (quadraticC p a * G - 1) ^ 3 * ZMod.stdAddChar (N := p) (-(a * (n : ZMod p))) =
        (G ^ 3 + 3 * G) * (quadraticC p a * ZMod.stdAddChar (N := p) (-(a * (n : ZMod p)))) -
          (3 * G ^ 2 + 1) * ZMod.stdAddChar (N := p) (-(a * (n : ZMod p))) := by
    have hs := quadraticC_sq p a (Finset.ne_of_mem_erase ha)
    have ht : quadraticC p a ^ 3 = quadraticC p a := by rw [pow_succ, hs, one_mul]
    ring_nf
    rw [hs, ht]
    ring
  have hT : (∑ a ∈ S, quadraticC p a * ZMod.stdAddChar (N := p) (-(a * (n : ZMod p)))) =
      quadraticC p (-(n : ZMod p)) * G := by
    have h0 : quadraticC p (0 : ZMod p) = 0 := by
      simp [quadraticC, MulChar.ringHomComp_apply]
    have ht := Finset.sum_erase_add (Finset.univ : Finset (ZMod p))
      (fun a => quadraticC p a * ZMod.stdAddChar (N := p) (a * (-(n : ZMod p))))
      (Finset.mem_univ 0)
    simp only [h0, zero_mul, add_zero] at ht
    have he : (∑ a : ZMod p, quadraticC p a * ZMod.stdAddChar (N := p) (a * (-(n : ZMod p)))) =
        gaussSum (quadraticC p) ((ZMod.stdAddChar (N := p)).mulShift (-(n : ZMod p))) := by
      simp only [gaussSum, AddChar.mulShift_apply, mul_comm]
    simpa only [S, ← mul_neg, he, quadratic_gauss_shift p hp, G] using ht
  have hR : (∑ a ∈ S, ZMod.stdAddChar (N := p) (-(a * (n : ZMod p)))) =
      if (n : ZMod p) = 0 then (p : ℂ) - 1 else -1 := by
    have ht := Finset.sum_erase_add (Finset.univ : Finset (ZMod p))
      (fun a => ZMod.stdAddChar (N := p) (a * (-(n : ZMod p)))) (Finset.mem_univ 0)
    have hs := AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := p))
      (-(n : ZMod p)) (ZMod.isPrimitive_stdAddChar p)
    simp only [zero_mul, AddChar.map_zero_eq_one] at ht
    rw [hs] at ht
    by_cases hn : (n : ZMod p) = 0 <;> simp [hn, S] at ht ⊢ <;> linear_combination ht
  rw [Task342h.A3_zmod_formula, Nat.totient_prime (Fact.out : p.Prime), hset]
  have hpp : 1 ≤ p := (Fact.out : p.Prime).one_le
  rw [Nat.cast_sub hpp, Nat.cast_one]
  have hsum : (∑ a ∈ S,
      (∑ x ∈ (Finset.univ : Finset (ZMod p)).filter IsUnit,
        ZMod.stdAddChar (N := p) (a * x * x)) ^ 3 *
        ZMod.stdAddChar (N := p) (-(a * (n : ZMod p)))) =
      (G ^ 3 + 3 * G) * (quadraticC p (-(n : ZMod p)) * G) -
        (3 * G ^ 2 + 1) * (if (n : ZMod p) = 0 then (p : ℂ) - 1 else -1) := by
    calc
      _ = ∑ a ∈ S, ((G ^ 3 + 3 * G) *
          (quadraticC p a * ZMod.stdAddChar (N := p) (-(a * (n : ZMod p)))) -
          (3 * G ^ 2 + 1) * ZMod.stdAddChar (N := p) (-(a * (n : ZMod p)))) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [reduced_quadratic_sum p hp a (Finset.ne_of_mem_erase ha)]
        exact hterm a ha
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hT, hR]
  rw [hset] at hsum
  rw [hsum]
  dsimp [G]
  ring

/-- Page 14 before display 47. The explicit Gauss expression yields a uniform
odd prime bound with constant 8. This uses no prime counting input. -/
theorem A3_odd_prime_bound (n p : ℕ) (hp : p.Prime) (hodd : 2 < p) :
    ‖A3 n p‖ ≤ 8 / (p : ℝ) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : (0 : ℝ) < p := by positivity
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hodd
  have hp2 : p ≠ 2 := by omega
  by_cases hpIs3 : p = 3
  · subst p
    have hb := Task403cI403d.A3_norm_le_totient n 3
    norm_num [Nat.totient_prime] at hb ⊢
    linarith
  have hp5 : (5 : ℝ) ≤ p := by
    have h4 : p ≠ 4 := by intro he; subst p; norm_num at hp
    exact_mod_cast (show 5 ≤ p by omega)
  let G := gaussSum (quadraticC p) (ZMod.stdAddChar (N := p))
  have hG : ‖G ^ 2‖ = (p : ℝ) := quadratic_gauss_sq_norm p hp2
  have hthree : ‖3 * G ^ 2 + 1‖ ≤ 3 * (p : ℝ) + 1 := by
    calc
      _ ≤ ‖(3 : ℂ) * G ^ 2‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = _ := by rw [norm_mul, hG]; norm_num
  have hden : ‖((p : ℂ) - 1) ^ 3‖ = ((p : ℝ) - 1) ^ 3 := by
    rw [norm_pow]
    congr 1
    rw [← Complex.ofReal_natCast p, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [A3_odd_prime_formula p hp2 n, norm_div, hden]
  change ‖(G ^ 3 + 3 * G) * (quadraticC p (-(n : ZMod p)) * G) -
    (3 * G ^ 2 + 1) * (if (n : ZMod p) = 0 then (p : ℂ) - 1 else -1)‖ /
      ((p : ℝ) - 1) ^ 3 ≤ _
  by_cases hn : (n : ZMod p) = 0
  · have hz : quadraticC p (0 : ZMod p) = 0 := by
      simp [quadraticC, MulChar.ringHomComp_apply]
    simp only [hn, neg_zero, hz, zero_mul, mul_zero, zero_sub, norm_neg, ite_true]
    have hpnorm : ‖(p : ℂ) - 1‖ = (p : ℝ) - 1 := by
      rw [← Complex.ofReal_natCast p, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [norm_mul, hpnorm]
    apply (div_le_iff₀ (pow_pos (by linarith : 0 < (p : ℝ) - 1) 3)).mpr
    have hnumer : ‖3 * G ^ 2 + 1‖ * ((p : ℝ) - 1) ≤
        (3 * (p : ℝ) + 1) * ((p : ℝ) - 1) :=
      mul_le_mul_of_nonneg_right hthree (by linarith)
    have hnum : ((3 : ℝ) * p + 1) * ((p : ℝ) - 1) ≤
        8 / (p : ℝ) * ((p : ℝ) - 1) ^ 3 := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hp0).mpr
      have hpos : 0 ≤ ((p : ℝ) - 3) * (5 * (p : ℝ) - 2) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith [mul_nonneg hpos (by linarith : 0 ≤ (p : ℝ) - 1)]
    exact hnumer.trans hnum
  · rw [ite_eq_right hn]
    have heq : (G ^ 3 + 3 * G) * (quadraticC p (-(n : ZMod p)) * G) -
        (3 * G ^ 2 + 1) * (-1) =
          quadraticC p (-(n : ZMod p)) * G ^ 2 * (G ^ 2 + 3) + (3 * G ^ 2 + 1) := by ring
    rw [heq]
    have hnumer : ‖quadraticC p (-(n : ZMod p)) * G ^ 2 * (G ^ 2 + 3) + (3 * G ^ 2 + 1)‖ ≤
        (p : ℝ) ^ 2 + 6 * (p : ℝ) + 1 := by
      have hplus : ‖G ^ 2 + 3‖ ≤ (p : ℝ) + 3 := by
        calc _ ≤ ‖G ^ 2‖ + ‖(3 : ℂ)‖ := norm_add_le _ _
             _ = _ := by rw [hG]; norm_num
      calc
        _ ≤ ‖quadraticC p (-(n : ZMod p)) * G ^ 2 * (G ^ 2 + 3)‖ + ‖3 * G ^ 2 + 1‖ := norm_add_le _ _
        _ ≤ (p : ℝ) * ((p : ℝ) + 3) + (3 * (p : ℝ) + 1) := by
          apply add_le_add _ hthree
          rw [norm_mul, norm_mul, hG]
          have hχ := quadraticC_norm_le p (-(n : ZMod p))
          exact mul_le_mul (mul_le_of_le_one_left hp0.le hχ) hplus
            (norm_nonneg _) hp0.le
        _ = _ := by ring
    apply (div_le_iff₀ (pow_pos (by linarith : 0 < (p : ℝ) - 1) 3)).mpr
    apply hnumer.trans
    have hpos : 0 ≤ ((p : ℝ) - 5) * (7 * (p : ℝ) ^ 2 + 5 * (p : ℝ) + 48) :=
      mul_nonneg (by linarith) (by positivity)
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hp0).mpr
    nlinarith


end LeanLab.KumchevLiu2007.Task403cI438g


/-! Inlined from Decomp438d.lean, unchanged except for the namespace prefix. -/
/-
Elementary local supplies for the three-square coefficient power bound.
Source page 13 properties i and ii and page 14 display 47.
The three local leaves have clean supplies. AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.KumchevLiu2007.Task403cI438d

open Real Complex Task129b Task129c
open scoped BigOperators

/-- LEAF. Page 13 property i. Schwarz page 83 Lemma 2.4.
Only the Chinese remainder factorization of one coefficient is required. -/
theorem A3_coprime_mul (n a b : ℕ) (hab : a.Coprime b) :
    A3 n (a * b) = A3 n a * A3 n b := by
  exact Task403cI438e.A3_coprime_mul n a b hab

/-- LEAF. Page 14 sentence before display 47. A coarse uniform odd prime
bound suffices. Schwarz page 83 display 2.11 gives the count route.
The constant 8 covers the prime 3 and the reciprocal square error. -/
theorem A3_odd_prime_bound (n p : ℕ) (hp : p.Prime) (hodd : 2 < p) :
    ‖A3 n p‖ ≤ 8 / (p : ℝ) := by
  exact Task403cI438g.A3_odd_prime_bound n p hp hodd

/-- LEAF. Page 13 property ii. Schwarz page 82 Lemma 2.1.
Odd prime powers vanish from exponent 2. Powers of 2 vanish from exponent 4.
This statement keeps the coefficients at 2, 4 and 8. -/
theorem A3_prime_power_vanish (n p k : ℕ) (hp : p.Prime)
    (hk : (p ≠ 2 ∧ 2 ≤ k) ∨ (p = 2 ∧ 4 ≤ k)) :
    A3 n (p ^ k) = 0 := by
  exact Task403cI438f.A3_prime_power_vanish n p k hp hk

/-- Page 13 display 45. The modulus one coefficient is one. -/
theorem A3_one (n : ℕ) : A3 n 1 = 1 := by
  simp [A3, U1534.gaussS, U1534.ee]

/-- Page 13 property ii. The elementary totient bound retains all three
dyadic coefficients and supplies the constant 64 after multiplication by q. -/
theorem A3_small_dyadic_bound (n k : ℕ) (hk : 1 ≤ k) (hk3 : k ≤ 3) :
    ‖A3 n (2 ^ k)‖ ≤ 64 / ((2 ^ k : ℕ) : ℝ) := by
  have hb := Task403cI403d.A3_norm_le_totient n (2 ^ k)
  have ht : ((Nat.totient (2 ^ k) : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.totient_le _)
  have hb' := hb.trans ht
  interval_cases k <;> norm_num at hb' ⊢ <;> linarith

/-- Page 14 display 47, local input for the composite estimate.
The odd prime bound and prime power vanishing are proved. -/
theorem A3_prime_power_bound (n p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    ‖A3 n (p ^ k)‖ ≤ 64 / ((p ^ k : ℕ) : ℝ) := by
  by_cases htwo : p = 2
  · subst p
    by_cases hsmall : k ≤ 3
    · exact A3_small_dyadic_bound n k hk hsmall
    · rw [A3_prime_power_vanish n 2 k hp (Or.inr ⟨rfl, by omega⟩), norm_zero]
      positivity
  · by_cases hone : k = 1
    · subst k
      simp only [pow_one]
      have hp2 := hp.two_le
      exact (A3_odd_prime_bound n p hp (by omega)).trans (by
        apply div_le_div_of_nonneg_right (by norm_num) (by positivity))
    · rw [A3_prime_power_vanish n p k hp (Or.inl ⟨htwo, by omega⟩), norm_zero]
      positivity

/-- Page 14 display 47. A numerical majorant with one constant per distinct
prime divisor. The even prime is counted once even when its exponent is 3. -/
noncomputable def coefficientMajorant (q : ℕ) : ℝ :=
  ∏ _p ∈ q.primeFactors, (64 : ℝ)

/-- Page 14 display 47. Multiplying the local prime power bounds gives a
composite bound from the three proved local coefficient inputs. -/
theorem coefficient_product_bound (n q : ℕ) (hq : 0 < q) :
    ‖A3 n q‖ ≤ coefficientMajorant q / (q : ℝ) := by
  have hall : ∀ q : ℕ, 0 < q → ‖A3 n q‖ ≤ coefficientMajorant q / (q : ℝ) := by
    intro q
    induction q using Nat.recOnPrimeCoprime with
    | zero => intro h; omega
    | prime_pow p k hp =>
      intro hq
      by_cases hk : k = 0
      · subst k
        simp [A3_one, coefficientMajorant]
      · rw [coefficientMajorant, Nat.primeFactors_prime_pow hk hp]
        simpa using A3_prime_power_bound n p k hp (Nat.pos_of_ne_zero hk)
    | coprime a b ha hb hab ih_a ih_b =>
      intro hq
      have ha0 : a ≠ 0 := by omega
      have hb0 : b ≠ 0 := by omega
      have hdis := hab.disjoint_primeFactors
      have hM : coefficientMajorant (a * b) = coefficientMajorant a * coefficientMajorant b := by
        simp only [coefficientMajorant, Nat.primeFactors_mul ha0 hb0, Finset.prod_union hdis]
      rw [A3_coprime_mul n a b hab, norm_mul, hM, Nat.cast_mul]
      calc
        _ ≤ (coefficientMajorant a / (a : ℝ)) * (coefficientMajorant b / (b : ℝ)) :=
          mul_le_mul (ih_a (by omega)) (ih_b (by omega)) (norm_nonneg _)
            ((norm_nonneg _).trans (ih_a (by omega)))
        _ = _ := by ring
  exact hall q hq

/-- Page 14 display 47 and page 15 third display. The conservative numerical
majorant has arbitrary positive power growth by separating finitely many primes. -/
theorem coefficientMajorant_power_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ q : ℕ, 0 < q →
      coefficientMajorant q ≤ K * (q : ℝ) ^ ε := by
  classical
  let N : ℕ := ⌈(64 : ℝ) ^ ε⁻¹⌉₊
  refine ⟨(64 : ℝ) ^ N, by positivity, ?_⟩
  intro q hq
  let S := q.primeFactors.filter (fun p => p < N)
  let T := q.primeFactors.filter (fun p => ¬ p < N)
  have hS : (∏ _p ∈ S, (64 : ℝ)) ≤ (64 : ℝ) ^ N := by
    rw [Finset.prod_const]
    apply pow_le_pow_right₀ (by norm_num)
    have hsub : S ⊆ Finset.range N := by
      intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    simpa using Finset.card_le_card hsub
  have hT : (∏ _p ∈ T, (64 : ℝ)) ≤ (q : ℝ) ^ ε := by
    calc
      _ ≤ ∏ p ∈ T, (p : ℝ) ^ ε := by
        apply Finset.prod_le_prod₀ (fun p hp => by positivity)
        intro p hp
        have hpN : (64 : ℝ) ^ ε⁻¹ ≤ (p : ℝ) :=
          (Nat.le_ceil _).trans (by
            exact_mod_cast (Nat.le_of_not_gt (Finset.mem_filter.mp hp).2))
        have hb := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 64 ^ ε⁻¹) hpN hε.le
        rwa [Real.rpow_inv_rpow (by norm_num) hε.ne'] at hb
      _ = (∏ p ∈ T, (p : ℝ)) ^ ε :=
        Real.finsetProd_rpow T (fun p => (p : ℝ)) (fun p hp => by positivity) ε
      _ ≤ (q : ℝ) ^ ε := by
        apply Real.rpow_le_rpow (by positivity) _ hε.le
        have hprod : ∏ p ∈ T, p ≤ q := by
          apply Nat.le_of_dvd hq
          exact (Finset.prod_dvd_prod_of_subset T q.primeFactors (fun p => p)
            (Finset.filter_subset _ _)).trans (Nat.prod_primeFactors_dvd q)
        have hc : ((∏ p ∈ T, p : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hprod
        simpa only [Nat.cast_prod] using hc
  rw [coefficientMajorant,
    ← Finset.prod_filter_mul_prod_filter_not q.primeFactors (fun p => p < N)]
  exact mul_le_mul hS hT (by positivity) (by positivity)

/-- Page 14 display 47. Exact Task403cI438c coefficient leaf from three elementary
local inputs and the proved numerical product bound. -/
theorem coefficient_power_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ n q : ℕ, 0 < q →
      ‖A3 n q‖ ≤ K * (q : ℝ) ^ (1 / 8 : ℝ) / (q : ℝ) := by
  obtain ⟨K, hK, hb⟩ := coefficientMajorant_power_bound (1 / 8 : ℝ) (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro n q hq
  exact (coefficient_product_bound n q hq).trans
    (div_le_div_of_nonneg_right (hb q hq) (by positivity))

end LeanLab.KumchevLiu2007.Task403cI438d


/-! Inlined from Decomp438i.lean, unchanged except for the namespace prefix. -/
/-
Finite smooth support for the three-square singular product.
Source page 14 display 50. AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.KumchevLiu2007.Task403cI438i

open Real Complex Task129b Task129c Task292c Task403c
open scoped BigOperators

/-- Page 14 display 50. A nonzero smooth coefficient divides the full support
four times the squarefree prime product. Powers at 2 through 8 are retained. -/
theorem smooth_coefficient_support (n q : ℕ) (hq : 0 < q) (Q : ℝ)
    (hs : ∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) ≤ Q) (hc : A3 n q ≠ 0) :
    q ∣ 4 * smoothModulus Q := by
  classical
  have hall : ∀ q : ℕ, 0 < q →
      (∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) ≤ Q) → A3 n q ≠ 0 →
        q ∣ 4 * smoothModulus Q := by
    intro q
    induction q using Nat.recOnPrimeCoprime with
    | zero => intro h; omega
    | prime_pow p k hp =>
      intro hq hs hc
      by_cases hk0 : k = 0
      · subst k
        simp
      have hk : 0 < k := Nat.pos_of_ne_zero hk0
      have hpQ : (p : ℝ) ≤ Q := hs p hp (dvd_pow_self _ hk0)
      have hpM : p ∣ smoothModulus Q := by
        apply Nat.dvd_of_mem_primeFactors
        rw [(Task342f.smoothModulus_facts Q).2]
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
          (Nat.lt_succ_iff.mpr (Nat.le_floor hpQ)), hp⟩
      by_cases htwo : p = 2
      · subst p
        have hk3 : k ≤ 3 := by
          by_contra he
          exact hc (Task403cI438f.A3_prime_power_vanish n 2 k hp (Or.inr ⟨rfl, by omega⟩))
        apply (pow_dvd_pow 2 hk3).trans
        obtain ⟨t, ht⟩ := hpM
        refine ⟨t, ?_⟩
        rw [ht]
        ring
      · have hk1 : k = 1 := by
          by_contra he
          exact hc (Task403cI438f.A3_prime_power_vanish n p k hp (Or.inl ⟨htwo, by omega⟩))
        simpa [hk1] using hpM.trans (dvd_mul_left (smoothModulus Q) 4)
    | coprime a b ha hb hab iha ihb =>
      intro hq hs hc
      have hca : A3 n a ≠ 0 := by
        intro hz
        apply hc
        rw [Task403cI438e.A3_coprime_mul n a b hab, hz, zero_mul]
      have hcb : A3 n b ≠ 0 := by
        intro hz
        apply hc
        rw [Task403cI438e.A3_coprime_mul n a b hab, hz, mul_zero]
      exact hab.mul_dvd_of_dvd_of_dvd
        (iha (by omega) (fun p hp hd => hs p hp (hd.trans (dvd_mul_right a b))) hca)
        (ihb (by omega) (fun p hp hd => hs p hp (hd.trans (dvd_mul_left b a))) hcb)
  exact hall q hq hs hc

/-- Page 14 display 50. When Q is at least 2, the smooth weighted coefficient
is exactly the divisor supported coefficient of four times the prime product. -/
theorem smooth_coefficient_dvd (n q : ℕ) (hq : 0 < q) (Q : ℝ) (hQ : 2 ≤ Q) :
    (smoothWeight q Q : ℂ) * A3 n q =
      if q ∣ 4 * smoothModulus Q then A3 n q else 0 := by
  classical
  have hM0 : smoothModulus Q ≠ 0 := (Task342f.smoothModulus_facts Q).1.ne_zero
  have hprime (p : ℕ) (hp : p.Prime) (hd : p ∣ 4 * smoothModulus Q) : (p : ℝ) ≤ Q := by
    rcases hp.dvd_mul.mp hd with h4 | hM
    · have h2 : p = 2 := by
        have hd2 : p ∣ 2 ^ 2 := by simpa using h4
        exact (Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow hd2) |>.resolve_left hp.ne_one
      subst p
      exact hQ
    · have hm := (Nat.mem_primeFactors.mpr ⟨hp, hM, hM0⟩)
      rw [(Task342f.smoothModulus_facts Q).2] at hm
      have hle : p ≤ ⌊Q⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hm).1)
      exact (Nat.cast_le.mpr hle).trans (Nat.floor_le (by linarith))
  by_cases hd : q ∣ 4 * smoothModulus Q
  · rw [ite_eq_left hd]
    have hs : smoothWeight q Q = 1 := by
      unfold smoothWeight
      exact ite_eq_left (fun p hp hpq => hprime p hp (hpq.trans hd))
    simp [hs]
  · rw [ite_eq_right hd]
    by_cases hs : ∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) ≤ Q
    · have hz : A3 n q = 0 := by
        by_contra hc
        exact hd (smooth_coefficient_support n q hq Q hs hc)
      simp [hz]
    · simp [smoothWeight, hs]

/-- Page 14 display 50. The three-square Euler product is the divisor sum
at four times the prime product when Q is at least 2. -/
theorem product3_divisor_sum (n : ℕ) (Q : ℝ) (hQ : 2 ≤ Q) :
    product3 n Q = ∑ q ∈ (4 * smoothModulus Q).divisors, A3 n q := by
  classical
  let S := (Finset.range (⌊Q⌋₊ + 1)).filter (fun p => p.Prime ∧ 2 < p)
  let O := ∏ p ∈ S, p
  have hS : ∀ p ∈ S, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2.1
  have hO0 : O ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => (hS p hp).ne_zero)
  have hpf : O.primeFactors = S := Nat.primeFactors_prod hS
  have hsq : Squarefree O := by
    have hs : ∀ T : Finset ℕ, (∀ p ∈ T, p.Prime) → Squarefree (∏ p ∈ T, p) := by
      intro T
      induction T using Finset.induction_on with
      | empty => simp
      | insert p T hp ih =>
        intro h
        have hprime := h p (Finset.mem_insert_self p T)
        have ht : ∀ r ∈ T, r.Prime := fun r hr => h r (Finset.mem_insert_of_mem hr)
        have hc : p.Coprime (∏ r ∈ T, r) := by
          apply Nat.Coprime.prod_right
          intro r hr
          exact (Nat.coprime_primes hprime (ht r hr)).mpr (by rintro rfl; exact hp hr)
        rw [Finset.prod_insert hp, Nat.squarefree_mul hc]
        exact ⟨hprime.squarefree, ih ht⟩
    exact hs S hS
  have h2not : ¬2 ∣ O := by
    intro hd
    have hm := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hd, hO0⟩
    rw [hpf] at hm
    have hgt := (Finset.mem_filter.mp hm).2.2
    omega
  have hcop : Nat.Coprime 8 O := by
    have hc : Nat.Coprime 2 O := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2not
    exact hc.pow_left 3
  have h2S : 2 ∉ S := by simp [S]
  have hprimes : (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime = insert 2 S := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, S]
    constructor
    · rintro ⟨hpq, hprime⟩
      by_cases hp2 : p = 2
      · exact Or.inl hp2
      · exact Or.inr ⟨hpq, hprime, by have := hprime.two_le; omega⟩
    · rintro (rfl | ⟨hpq, hp, hgt⟩)
      · exact ⟨Nat.lt_succ_iff.mpr (Nat.le_floor hQ), Nat.prime_two⟩
      · exact ⟨hpq, hp⟩
  have hM : 4 * smoothModulus Q = 8 * O := by
    rw [smoothModulus, hprimes, Finset.prod_insert h2S]
    dsimp [O]
    ring
  let f : ArithmeticFunction ℂ := ⟨A3 n, by simp [A3]⟩
  have hf : f.IsMultiplicative :=
    ⟨Task403cI438d.A3_one n, fun {a b} hab => Task403cI438e.A3_coprime_mul n a b hab⟩
  have hg := hf.mul (ArithmeticFunction.isMultiplicative_zeta.natCast (R := ℂ))
  have hmul : (∑ q ∈ (8 * O).divisors, A3 n q) =
      (∑ q ∈ Nat.divisors 8, A3 n q) * (∑ q ∈ O.divisors, A3 n q) := by
    have hm := hg.map_mul_of_coprime hcop
    simp only [ArithmeticFunction.coe_mul_zeta_apply] at hm
    exact hm
  have h8 : (∑ q ∈ Nat.divisors 8, A3 n q) = 1 + A3 n 2 + A3 n 4 + A3 n 8 := by
    have hd : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [hd]
    simp [Task403cI438d.A3_one]
    ring
  have hO : (∑ q ∈ O.divisors, A3 n q) = ∏ p ∈ S, (1 + A3 n p) := by
    simpa [hpf, f] using (hf.prodPrimeFactors_one_add_of_squarefree hsq).symm
  rw [hM, hmul, h8, hO]
  simp only [product3, ite_eq_left hQ, S]

/-- Page 14 display 50. The Euler product is the full finite smooth
coefficient sum with the even prime powers through 8. -/
theorem product3_smooth_sum (n : ℕ) (Q : ℝ) (hQ : 2 ≤ Q) :
    product3 n Q = ∑ q ∈ Finset.Icc 1 (4 * smoothModulus Q),
      (smoothWeight q Q : ℂ) * A3 n q := by
  classical
  rw [product3_divisor_sum n Q hQ]
  have hM0 : 4 * smoothModulus Q ≠ 0 :=
    Nat.mul_ne_zero (by norm_num) (Task342f.smoothModulus_facts Q).1.ne_zero
  have hdiv : (Finset.Icc 1 (4 * smoothModulus Q)).filter
      (fun q => q ∣ 4 * smoothModulus Q) = (4 * smoothModulus Q).divisors := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨hq, hd⟩
      exact ⟨hd, hM0⟩
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hM0),
        Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hd⟩, hd⟩
  rw [← hdiv, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  exact (smooth_coefficient_dvd n q (Finset.mem_Icc.mp hq).1 Q hQ).symm

/-- Page 14 display 50. The finite smooth expansion also covers positive Q
below 2. In that case the only surviving modulus is 1. -/
theorem product3_smooth_sum_all (n : ℕ) (Q : ℝ) (hQ : 0 < Q) :
    product3 n Q = ∑ q ∈ Finset.Icc 1 (4 * smoothModulus Q),
      (smoothWeight q Q : ℂ) * A3 n q := by
  classical
  by_cases hQ2 : 2 ≤ Q
  · exact product3_smooth_sum n Q hQ2
  have hQlt : Q < 2 := lt_of_not_ge hQ2
  have hemp : (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hprange, hp⟩
    have hle : (p : ℝ) ≤ Q := (Nat.cast_le.mpr
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hprange))).trans (Nat.floor_le hQ.le)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have hemp' : (Finset.range (⌊Q⌋₊ + 1)).filter (fun p => p.Prime ∧ 2 < p) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hm : p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime :=
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.1⟩
    rw [hemp] at hm
    exact Finset.notMem_empty _ hm
  have hM : smoothModulus Q = 1 := by simp [smoothModulus, hemp]
  have hw (q : ℕ) (hq : 0 < q) (hne : q ≠ 1) : smoothWeight q Q = 0 := by
    unfold smoothWeight
    apply if_neg
    intro hs
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have hle := hs p hp hpd
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  simp only [product3, ite_eq_right hQ2, hemp', Finset.prod_empty, mul_one, hM]
  symm
  trans (smoothWeight 1 Q : ℂ) * A3 n 1
  · apply Finset.sum_eq_single 1
    · intro q hq hne
      rw [hw q (Finset.mem_Icc.mp hq).1 hne]
      simp
    · intro hnot
      exact False.elim (hnot (by norm_num))
  · simp [smoothWeight, Task403cI438d.A3_one, Nat.not_prime_one]

/-- Page 14 display 50. Exact Task403cI438a finite remainder supply, including
positive cutoffs below 2 and the full even prime support through 8. -/
theorem smooth_remainder_identity (n : ℕ) (P Q T : ℝ)
    (hP : 0 < P) (hPQ : P ≤ Q) (hQT : Q ≤ T) :
    (series3 n P - product3 n Q) - tail3 n P T Q =
      -(∑ q ∈ Finset.Ioc ⌊T⌋₊ (4 * smoothModulus Q),
        (smoothWeight q Q : ℂ) * A3 n q) := by
  classical
  have hQ : 0 < Q := hP.trans_le hPQ
  let w : ℕ → ℂ := fun q => (smoothWeight q Q : ℂ) * A3 n q
  have hser : series3 n P = ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, w q := by
    unfold series3
    apply Finset.sum_congr rfl
    intro q hq
    have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
    have hs : smoothWeight q Q = 1 := by
      unfold smoothWeight
      apply if_pos
      intro p hp hpq
      have hpq' := Nat.le_of_dvd hqpos hpq
      exact ((Nat.cast_le.mpr (hpq'.trans (Finset.mem_Icc.mp hq).2)).trans
        (Nat.floor_le hP.le)).trans hPQ
    simp [w, hs]
  have htail : tail3 n P T Q = -∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊T⌋₊, w q := by
    simp only [tail3, w, neg_mul, Finset.sum_neg_distrib]
  have hPT : ⌊P⌋₊ ≤ ⌊T⌋₊ := Nat.floor_mono (hPQ.trans hQT)
  have hsplit : (∑ q ∈ Finset.Icc 1 ⌊P⌋₊, w q) +
      (∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊T⌋₊, w q) = ∑ q ∈ Finset.Icc 1 ⌊T⌋₊, w q := by
    have he := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 ⌊T⌋₊)
      (fun q => q ≤ ⌊P⌋₊) w
    convert he using 2 <;> congr 1 <;> ext q <;>
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] <;> omega
  have hsum : (∑ q ∈ Finset.Icc 1 ⌊T⌋₊, w q) +
      (∑ q ∈ Finset.Ioc ⌊T⌋₊ (4 * smoothModulus Q), w q) = product3 n Q := by
    rw [product3_smooth_sum_all n Q hQ]
    change _ = ∑ q ∈ Finset.Icc 1 (4 * smoothModulus Q), w q
    by_cases hTM : ⌊T⌋₊ ≤ 4 * smoothModulus Q
    · have he := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (4 * smoothModulus Q))
        (fun q => q ≤ ⌊T⌋₊) w
      convert he using 2 <;> congr 1 <;> ext q <;>
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] <;> omega
    · have hMT : 4 * smoothModulus Q ≤ ⌊T⌋₊ := by omega
      rw [Finset.Ioc_eq_empty_of_le hMT, Finset.sum_empty, add_zero]
      symm
      apply Finset.sum_subset
      · intro q hq
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hq).1, (Finset.mem_Icc.mp hq).2.trans hMT⟩
      · intro q hq hnot
        have hqpos := (Finset.mem_Icc.mp hq).1
        have hMq : 4 * smoothModulus Q < q := by
          simp only [Finset.mem_Icc, not_and, not_le] at hnot
          exact hnot hqpos
        dsimp [w]
        by_cases hs : ∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) ≤ Q
        · have hz : A3 n q = 0 := by
            by_contra hc
            have hd := smooth_coefficient_support n q hqpos Q hs hc
            have hM0 : 0 < 4 * smoothModulus Q := Nat.mul_pos (by norm_num)
              (Nat.pos_of_ne_zero (Task342f.smoothModulus_facts Q).1.ne_zero)
            exact (Nat.not_le_of_gt hMq) (Nat.le_of_dvd hM0 hd)
          simp [hz]
        · simp [smoothWeight, hs]
  rw [hser, htail]
  linear_combination hsplit + hsum


end LeanLab.KumchevLiu2007.Task403cI438i


/-! Inlined from Decomp438j.lean, unchanged except for the namespace prefix. -/
/-
Numerical smooth tail supply for three-square truncation.
Source page 14 below display 50. The numerical leaf remains OPEN.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.KumchevLiu2007.Task403cI438j

open Real Complex Task129b Task129c Task292c Task403cI438d
open scoped BigOperators

private theorem frac_local_bound (Q : ℝ) (hQ : 0 < Q) (p : ℕ)
    (hp : p.Prime) (hpQ : (p : ℝ) ≤ Q) :
    0 < (p : ℝ) ^ (1 - 1 / (2 * max 1 (Real.log Q))) - 1 ∧
      64 / ((p : ℝ) ^ (1 - 1 / (2 * max 1 (Real.log Q))) - 1) ≤ 768 / (p : ℝ) := by
  let V := max 1 (Real.log Q)
  let δ := 1 / (2 * V)
  let s := 1 - δ
  have hV1 : 1 ≤ V := le_max_left _ _
  have hVpos : 0 < V := by linarith
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hδ : δ ≤ (1 / 2 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (by dsimp [V] at *; linarith)
  have hs : (1 / 2 : ℝ) ≤ s := by dsimp [s]; linarith
  have hlog : Real.log (p : ℝ) ≤ V :=
    (Real.log_le_log hp0 hpQ).trans (le_max_right _ _)
  have hδlog : Real.log (p : ℝ) * δ ≤ 1 := by
    dsimp [δ]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 2 * V)).mpr
    linarith
  have hexp : Real.exp (Real.log (p : ℝ) * δ) ≤ 3 := by
    exact (Real.exp_le_exp.mpr hδlog).trans (by linarith [Real.exp_one_lt_d9])
  have hprod : (p : ℝ) ^ s * Real.exp (Real.log (p : ℝ) * δ) = (p : ℝ) := by
    rw [Real.rpow_def_of_pos hp0, ← Real.exp_add]
    have he : Real.log (p : ℝ) * s + Real.log (p : ℝ) * δ = Real.log (p : ℝ) := by
      dsimp [s]
      ring
    rw [he, Real.exp_log hp0]
  have hp3 : (p : ℝ) / 3 ≤ (p : ℝ) ^ s := by
    have hh := mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hp0.le s)
    rw [hprod] at hh
    linarith
  have hsqrt : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hp43 : (4 / 3 : ℝ) ≤ (p : ℝ) ^ s := by
    calc
      _ ≤ Real.sqrt 2 := hsqrt
      _ = (2 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 2
      _ ≤ (p : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hp2 (by norm_num)
      _ ≤ (p : ℝ) ^ s := Real.rpow_le_rpow_of_exponent_le (by linarith) hs
  have hden : (p : ℝ) / 12 ≤ (p : ℝ) ^ s - 1 := by linarith
  have hdenpos : 0 < (p : ℝ) ^ s - 1 := lt_of_lt_of_le (by positivity) hden
  change 0 < (p : ℝ) ^ s - 1 ∧ 64 / ((p : ℝ) ^ s - 1) ≤ 768 / (p : ℝ)
  refine ⟨hdenpos, ?_⟩
  apply (div_le_div_iff₀ hdenpos hp0).mpr
  nlinarith

/-! ### Uniform numerical Euler product bound (port of EulerProduct447) -/

private theorem frac_euler_product_bound :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ Q : ℝ, 0 < Q →
      (∏ p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime,
        (1 + 64 / ((p : ℝ) ^ (1 - 1 / (2 * max 1 (Real.log Q))) - 1))) ≤
        C * (max 1 (Real.log Q)) ^ D := by
  classical
  refine ⟨Real.exp 9216, 768, Real.exp_pos _, by norm_num, ?_⟩
  intro Q hQ
  let S := (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime
  let s := 1 - 1 / (2 * max 1 (Real.log Q))
  by_cases hQ2 : 2 ≤ Q
  · let N := ⌊Q⌋₊
    have hN2 : 2 ≤ N := Nat.le_floor hQ2
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hNQ : (N : ℝ) ≤ Q := Nat.floor_le hQ.le
    have hlocal (p : ℕ) (hp : p ∈ S) :
        0 < 1 + 64 / ((p : ℝ) ^ s - 1) ∧
          Real.log (1 + 64 / ((p : ℝ) ^ s - 1)) ≤ 768 * (1 / (p : ℝ)) := by
      have hprime := (Finset.mem_filter.mp hp).2
      have hpN : p ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
      have hpQ : (p : ℝ) ≤ Q := (Nat.cast_le.mpr hpN).trans hNQ
      obtain ⟨hd, hb⟩ := frac_local_bound Q hQ p hprime hpQ
      change 0 < (p : ℝ) ^ s - 1 at hd
      change 64 / ((p : ℝ) ^ s - 1) ≤ 768 / (p : ℝ) at hb
      have hpos : 0 < 1 + 64 / ((p : ℝ) ^ s - 1) := by positivity
      refine ⟨hpos, ?_⟩
      have hh := Real.log_le_sub_one_of_pos hpos
      have hh' : Real.log (1 + 64 / ((p : ℝ) ^ s - 1)) ≤ 64 / ((p : ℝ) ^ s - 1) := by
        linarith
      convert hh'.trans hb using 1 <;> ring
    have hsum : (∑ p ∈ S, 1 / (p : ℝ)) ≤ Real.log (Real.log (N : ℝ)) + 12 := by
      have hsub : S ⊆ (Finset.Icc 1 N).filter Nat.Prime := by
        intro p hp
        obtain ⟨hpr, hprime⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
          ⟨hprime.one_le, Nat.lt_succ_iff.mp (Finset.mem_range.mp hpr)⟩, hprime⟩
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp hn => by positivity)).trans
        (LeanLab.PNTSieve.Mertens.sum_inv_primes_le N hN2)
    have hprodpos : 0 < ∏ p ∈ S, (1 + 64 / ((p : ℝ) ^ s - 1)) :=
      Finset.prod_pos (fun p hp => (hlocal p hp).1)
    have hlogprod : Real.log (∏ p ∈ S, (1 + 64 / ((p : ℝ) ^ s - 1))) ≤
        768 * (Real.log (Real.log (N : ℝ)) + 12) := by
      rw [Real.log_prod (fun p hp => (hlocal p hp).1.ne')]
      calc
        _ ≤ ∑ p ∈ S, 768 * (1 / (p : ℝ)) := Finset.sum_le_sum (fun p hp => (hlocal p hp).2)
        _ = 768 * ∑ p ∈ S, 1 / (p : ℝ) := (Finset.mul_sum _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by norm_num)
    have hprod : (∏ p ∈ S, (1 + 64 / ((p : ℝ) ^ s - 1))) ≤
        Real.exp 9216 * (Real.log (N : ℝ)) ^ (768 : ℕ) := by
      have hh := (Real.log_le_iff_le_exp hprodpos).mp hlogprod
      have he : Real.exp (768 * (Real.log (Real.log (N : ℝ)) + 12)) =
          Real.exp 9216 * (Real.log (N : ℝ)) ^ (768 : ℕ) := by
        rw [mul_add, Real.exp_add, show (768 : ℝ) = ((768 : ℕ) : ℝ) by norm_num,
          Real.exp_nat_mul, Real.exp_log hlogN]
        norm_num
        ring
      exact hh.trans_eq he
    calc
      _ ≤ Real.exp 9216 * (Real.log (N : ℝ)) ^ (768 : ℕ) := hprod
      _ ≤ Real.exp 9216 * (max 1 (Real.log Q)) ^ (768 : ℕ) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply pow_le_pow_left₀ hlogN.le
        exact (Real.log_le_log hNpos hNQ).trans (le_max_right _ _)
      _ = _ := by norm_num
  · have hS : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hprime := (Finset.mem_filter.mp hp).2
      have hpN : p ≤ ⌊Q⌋₊ :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
      have hpQ : (p : ℝ) ≤ Q := (Nat.cast_le.mpr hpN).trans (Nat.floor_le hQ.le)
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
      linarith
    change (∏ p ∈ S, (1 + 64 / ((p : ℝ) ^ s - 1))) ≤ _
    rw [hS, Finset.prod_empty]
    have hC : 1 ≤ Real.exp 9216 := Real.one_le_exp (by norm_num)
    have hV : 1 ≤ (max 1 (Real.log Q)) ^ (768 : ℝ) :=
      Real.one_le_rpow (le_max_left _ _) (by norm_num)
    nlinarith

/-! ### Finite Euler comparison (port of SmoothEuler447, no new definitions) -/

private theorem wr_nonneg (s : ℝ) (q : ℕ) : 0 ≤ coefficientMajorant q / (q : ℝ) ^ s := by
  unfold coefficientMajorant
  positivity

private theorem wr_one (s : ℝ) : coefficientMajorant 1 / ((1 : ℕ) : ℝ) ^ s = 1 := by
  simp [coefficientMajorant]

private theorem wr_mul (s : ℝ) (hs : 0 < s) (a b : ℕ) (hab : a.Coprime b) :
    coefficientMajorant (a * b) / ((a * b : ℕ) : ℝ) ^ s =
      (coefficientMajorant a / (a : ℝ) ^ s) * (coefficientMajorant b / (b : ℝ) ^ s) := by
  by_cases ha : a = 0
  · subst a
    simp [Real.zero_rpow hs.ne']
  by_cases hb : b = 0
  · subst b
    simp [Real.zero_rpow hs.ne']
  have hM : coefficientMajorant (a * b) = coefficientMajorant a * coefficientMajorant b := by
    simp only [coefficientMajorant, Nat.primeFactors_mul ha hb,
      Finset.prod_union hab.disjoint_primeFactors]
  simp only [hM, Nat.cast_mul, Real.mul_rpow (by positivity : (0 : ℝ) ≤ a)
    (by positivity : (0 : ℝ) ≤ b)]
  ring

private theorem wr_prime_power_hasSum (p : ℕ) (hp : p.Prime) (s : ℝ) (hs : 0 < s) :
    HasSum (fun k : ℕ => coefficientMajorant (p ^ k) / ((p ^ k : ℕ) : ℝ) ^ s)
      (1 + 64 / ((p : ℝ) ^ s - 1)) := by
  classical
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hps : 1 < (p : ℝ) ^ s := Real.one_lt_rpow (by exact_mod_cast hp.one_lt) hs
  let r := ((p : ℝ) ^ s)⁻¹
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; exact inv_lt_one_of_one_lt₀ hps
  have hterm (k : ℕ) : coefficientMajorant (p ^ k) / ((p ^ k : ℕ) : ℝ) ^ s =
      64 * r ^ k - (if k = 0 then 63 else 0) := by
    by_cases hk : k = 0
    · subst k
      norm_num [coefficientMajorant]
    · have hpow : (((p ^ k : ℕ) : ℝ)) ^ s = ((p : ℝ) ^ s) ^ k := by
        rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le,
          mul_comm (k : ℝ) s, Real.rpow_mul hp0.le, Real.rpow_natCast]
      simp only [coefficientMajorant, Nat.primeFactors_prime_pow hk hp,
        Finset.prod_singleton, hpow, hk, ite_false, sub_zero]
      dsimp [r]
      rw [inv_pow, div_eq_mul_inv]
  have hh := ((hasSum_geometric_of_lt_one hr0 hr1).mul_left (64 : ℝ)).sub
    (hasSum_ite_eq (0 : ℕ) (63 : ℝ))
  have he : 64 * (1 - r)⁻¹ - 63 = 1 + 64 / ((p : ℝ) ^ s - 1) := by
    dsimp [r]
    have hpos : 0 < (p : ℝ) ^ s := by positivity
    field_simp [ne_of_gt hpos, ne_of_gt (sub_pos.mpr hps)]
    <;> ring
  rw [he] at hh
  simpa only [← hterm] using hh

private theorem smooth_moment_euler_bound (Q : ℝ) (M : ℕ) (hQ : 0 < Q) (s : ℝ) (hs : 0 < s) :
    (∑ q ∈ Finset.Icc 1 M,
      smoothWeight q Q * coefficientMajorant q / (q : ℝ) ^ s) ≤
      ∏ p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime,
        (1 + 64 / ((p : ℝ) ^ s - 1)) := by
  classical
  let S := (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime
  have hsum (p : ℕ) (hp : p.Prime) :
      Summable (fun k : ℕ => ‖coefficientMajorant (p ^ k) / ((p ^ k : ℕ) : ℝ) ^ s‖) := by
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (wr_nonneg s _)]
    exact (wr_prime_power_hasSum p hp s hs).summable
  have H := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun q : ℕ => coefficientMajorant q / (q : ℝ) ^ s)
    (wr_one s) (fun {a b} hab => wr_mul s hs a b hab) (fun {p} hp => hsum p hp) S).2
  have hfilter : S.filter Nat.Prime = S := by
    exact Finset.filter_eq_self.mpr (fun p hp => (Finset.mem_filter.mp hp).2)
  rw [hfilter] at H
  have hprod : (∏ p ∈ S, ∑' k : ℕ, coefficientMajorant (p ^ k) / ((p ^ k : ℕ) : ℝ) ^ s) =
      ∏ p ∈ S, (1 + 64 / ((p : ℝ) ^ s - 1)) := by
    apply Finset.prod_congr rfl
    intro p hp
    exact (wr_prime_power_hasSum p (Finset.mem_filter.mp hp).2 s hs).tsum_eq
  rw [hprod] at H
  let T := (Finset.Icc 1 M).filter (fun q => ∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) ≤ Q)
  have hT (q : ℕ) (hq : q ∈ T) : q ∈ Nat.factoredNumbers S := by
    apply Nat.mem_factoredNumbers'.mpr
    intro p hp hpq
    have hpQ := (Finset.mem_filter.mp hq).2 p hp hpq
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (Nat.lt_succ_iff.mpr (Nat.le_floor hpQ)), hp⟩
  have he : (∑ q ∈ Finset.Icc 1 M,
      smoothWeight q Q * coefficientMajorant q / (q : ℝ) ^ s) =
      ∑ q ∈ T, coefficientMajorant q / (q : ℝ) ^ s := by
    simp only [smoothWeight, ite_mul, one_mul, zero_mul, ite_div, zero_div]
    rw [← Finset.sum_filter]
  rw [he]
  change (∑ q ∈ T, coefficientMajorant q / (q : ℝ) ^ s) ≤
    ∏ p ∈ S, (1 + 64 / ((p : ℝ) ^ s - 1))
  rw [← Finset.sum_subtype_of_mem (fun q => coefficientMajorant q / (q : ℝ) ^ s) hT]
  exact (Summable.sum_le_tsum (T.subtype (fun q => q ∈ Nat.factoredNumbers S))
    (fun q hq => wr_nonneg s q) H.summable).trans_eq H.tsum_eq

/-! ### Fractional smooth moment (port of Decomp447c) -/

private theorem smooth_fractional_moment :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ (Q : ℝ) (M : ℕ), 0 < Q →
      (∑ q ∈ Finset.Icc 1 M,
        smoothWeight q Q * coefficientMajorant q /
          (q : ℝ) ^ (1 - 1 / (2 * max 1 (Real.log Q)))) ≤
        C * (max 1 (Real.log Q)) ^ D := by
  obtain ⟨C, D, hC, hD, hb⟩ := frac_euler_product_bound
  refine ⟨C, D, hC, hD, ?_⟩
  intro Q M hQ
  have hV : (1 : ℝ) ≤ max 1 (Real.log Q) := le_max_left _ _
  have hs : 0 < 1 - 1 / (2 * max 1 (Real.log Q)) := by
    have hh : 1 / (2 * max 1 (Real.log Q)) ≤ (1 / 2 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  exact (smooth_moment_euler_bound Q M hQ _ hs).trans (hb Q hQ)

/-! ### Finite Rankin inequality (port of Decomp447b) -/

private theorem weighted_rankin_tail (w : ℕ → ℝ) (hw : ∀ q, 0 ≤ w q)
    (T δ : ℝ) (hT : 0 < T) (hδ : 0 ≤ δ) (M : ℕ) :
    (∑ q ∈ Finset.Ioc ⌊T⌋₊ M, w q / (q : ℝ)) ≤
      (∑ q ∈ Finset.Icc 1 M, w q / (q : ℝ) ^ (1 - δ)) / T ^ δ := by
  have hpow : 0 < T ^ δ := Real.rpow_pos_of_pos hT δ
  calc
    _ ≤ ∑ q ∈ Finset.Ioc ⌊T⌋₊ M, (w q / (q : ℝ) ^ (1 - δ)) / T ^ δ := by
      apply Finset.sum_le_sum
      intro q hq
      have hqT : T < (q : ℝ) := (Nat.floor_lt hT.le).mp (Finset.mem_Ioc.mp hq).1
      have hq0 : (0 : ℝ) < q := hT.trans hqT
      have hp : T ^ δ ≤ (q : ℝ) ^ δ := Real.rpow_le_rpow hT.le hqT.le hδ
      have he : (q : ℝ) ^ (1 - δ) * (q : ℝ) ^ δ = q := by
        rw [← Real.rpow_add hq0]
        simp
      calc
        _ = (w q / (q : ℝ) ^ (1 - δ)) / (q : ℝ) ^ δ := by
          rw [div_div, he]
        _ ≤ _ :=
          div_le_div_of_nonneg_left (div_nonneg (hw q) (Real.rpow_nonneg hq0.le _)) hpow hp
    _ = (∑ q ∈ Finset.Ioc ⌊T⌋₊ M, w q / (q : ℝ) ^ (1 - δ)) / T ^ δ := by
      rw [Finset.sum_div]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hpow.le
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Ioc.mp hq).1; omega,
          (Finset.mem_Ioc.mp hq).2⟩
      · intro q hq hn
        exact div_nonneg (hw q) (Real.rpow_nonneg (by positivity) _)

/-! ### Real parameter absorption (port of Rankin447) -/

private theorem rankin_parameter_absorption (D B ε : ℝ) (hD : 0 ≤ D)
    (hB : 0 < B) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (max 1 (Real.log Q)) ^ D /
        (y ^ (1 / 3 : ℝ)) ^ (1 / (2 * max 1 (Real.log Q))) ≤
          C / Real.log x ^ B := by
  let η := min ε (1 / 2 : ℝ)
  have hη : 0 < η := lt_min hε (by norm_num)
  have hηε : η ≤ ε := min_le_left _ _
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hDB : 0 < D + B := by linarith
  have hc : 0 < η / (6 * (D + B)) := by positivity
  obtain ⟨L0, hb⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_atTop hη).bound hc)
  refine ⟨1, max 2 (Real.exp (max L0 2)), by norm_num, le_max_left _ _, ?_⟩
  intro x y Q hx hy _hyx hQpos hQ
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hxpos : 0 < x := by linarith
  let L := Real.log x
  have hL : max L0 2 ≤ L := by
    apply (Real.le_log_iff_exp_le hxpos).mpr
    exact (le_max_right _ _).trans hx
  have hL2 : 2 ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hlog : Real.log L ≤ η / (6 * (D + B)) * L ^ η := by
    have hh := hb L ((le_max_left _ _).trans hL)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL1),
      abs_of_pos (Real.rpow_pos_of_pos hLpos _)] using hh
  have hlogs : (D + B) * Real.log L ≤ η / 6 * L ^ η := by
    have hh := mul_le_mul_of_nonneg_left hlog hDB.le
    have he : (D + B) * (η / (6 * (D + B))) = η / 6 := by field_simp
    calc
      _ ≤ (D + B) * (η / (6 * (D + B)) * L ^ η) := hh
      _ = _ := by rw [← mul_assoc, he]
  let V := max 1 (Real.log Q)
  have hV1 : 1 ≤ V := le_max_left _ _
  have hVpos : 0 < V := by linarith
  have hV : V ≤ L ^ (1 - η) := by
    apply max_le
    · exact Real.one_le_rpow hL1 (by linarith)
    · have hlogQ : Real.log Q ≤ L ^ (1 - ε) :=
        (Real.log_le_iff_le_exp hQpos).mpr hQ
      exact hlogQ.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  have hVL : V ≤ L := by
    calc
      _ ≤ L ^ (1 - η) := hV
      _ ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ = L := Real.rpow_one L
  have hscale : V * L ^ η ≤ L := by
    calc
      _ ≤ L ^ (1 - η) * L ^ η :=
        mul_le_mul_of_nonneg_right hV (Real.rpow_nonneg hLpos.le _)
      _ = L := by rw [← Real.rpow_add hLpos]; simp
  have hypos : 0 < y := (Real.rpow_pos_of_pos hxpos ε).trans_le hy
  have hlogy : η * L ≤ Real.log y := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hxpos ε) hy
    rw [Real.log_rpow hxpos] at hh
    exact (mul_le_mul_of_nonneg_right hηε hLpos.le).trans hh
  have harg0 : η / 6 * L ^ η ≤ Real.log y / (6 * V) := by
    apply (le_div_iff₀ (by positivity : 0 < 6 * V)).mpr
    have hh := mul_le_mul_of_nonneg_left hscale hη.le
    nlinarith
  have hT : 0 < y ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hypos _
  have harg : Real.exp (η / 6 * L ^ η) ≤
      (y ^ (1 / 3 : ℝ)) ^ (1 / (2 * V)) := by
    rw [Real.rpow_def_of_pos hT]
    apply Real.exp_le_exp.mpr
    rw [Real.log_rpow hypos]
    convert harg0 using 1 <;> ring
  have hnum : V ^ D * L ^ B ≤ Real.exp (η / 6 * L ^ η) := by
    calc
      _ ≤ L ^ D * L ^ B :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hVpos.le hVL hD)
          (Real.rpow_nonneg hLpos.le _)
      _ = L ^ (D + B) := (Real.rpow_add hLpos _ _).symm
      _ = Real.exp ((D + B) * Real.log L) := by
        rw [Real.rpow_def_of_pos hLpos]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr hlogs
  change V ^ D / (y ^ (1 / 3 : ℝ)) ^ (1 / (2 * V)) ≤ 1 / L ^ B
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hT _) (Real.rpow_pos_of_pos hLpos B)).mpr
  simpa only [one_mul] using hnum.trans harg

/-! ### The leaf -/

private theorem smooth_reciprocal_tail_proved (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ q ∈ Finset.Ioc ⌊y ^ (1 / 3 : ℝ)⌋₊ (4 * smoothModulus Q),
        smoothWeight q Q * (coefficientMajorant q / (q : ℝ))) ≤
          C / Real.log x ^ (A / 2) := by
  obtain ⟨C, D, hC, hD, hm⟩ := smooth_fractional_moment
  obtain ⟨K, x0, hK, hx0, hk⟩ :=
    rankin_parameter_absorption D (A / 2) ε hD (by linarith) hε
  refine ⟨C * K, x0, mul_pos hC hK, hx0, ?_⟩
  intro x y Q hx hy hyx hQpos hQ
  have hxpos : (0 : ℝ) < x := by linarith
  have hT : 0 < y ^ (1 / 3 : ℝ) := by
    have hypos : 0 < y := (Real.rpow_pos_of_pos hxpos ε).trans_le hy
    exact Real.rpow_pos_of_pos hypos _
  have hδ : 0 ≤ 1 / (2 * max 1 (Real.log Q)) := by positivity
  have hw (q : ℕ) : 0 ≤ smoothWeight q Q * coefficientMajorant q := by
    have hsw : 0 ≤ smoothWeight q Q := by unfold smoothWeight; split <;> norm_num
    exact mul_nonneg hsw (by unfold coefficientMajorant; positivity)
  calc
    _ = ∑ q ∈ Finset.Ioc ⌊y ^ (1 / 3 : ℝ)⌋₊ (4 * smoothModulus Q),
        (smoothWeight q Q * coefficientMajorant q) / (q : ℝ) := by
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ (∑ q ∈ Finset.Icc 1 (4 * smoothModulus Q),
        smoothWeight q Q * coefficientMajorant q /
          (q : ℝ) ^ (1 - 1 / (2 * max 1 (Real.log Q)))) /
        (y ^ (1 / 3 : ℝ)) ^ (1 / (2 * max 1 (Real.log Q))) :=
      weighted_rankin_tail _ hw _ _ hT hδ _
    _ ≤ (C * (max 1 (Real.log Q)) ^ D) /
        (y ^ (1 / 3 : ℝ)) ^ (1 / (2 * max 1 (Real.log Q))) :=
      div_le_div_of_nonneg_right (hm Q _ hQpos) (by positivity)
    _ = C * ((max 1 (Real.log Q)) ^ D /
        (y ^ (1 / 3 : ℝ)) ^ (1 / (2 * max 1 (Real.log Q)))) := by ring
    _ ≤ C * (K / Real.log x ^ (A / 2)) :=
      mul_le_mul_of_nonneg_left (hk x y Q hx hy hyx hQpos hQ) hC.le
    _ = _ := by ring

/-- LEAF. Page 14 below display 50, using Lemma 3.5 on page 12.
This is only a numerical weighted smooth reciprocal tail. There is no A3,
n, Euler product, series error or interval average. The proved conservative
majorant has one factor 64 per distinct prime divisor. -/
theorem smooth_reciprocal_tail (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ q ∈ Finset.Ioc ⌊y ^ (1 / 3 : ℝ)⌋₊ (4 * smoothModulus Q),
        smoothWeight q Q * (coefficientMajorant q / (q : ℝ))) ≤
          C / Real.log x ^ (A / 2) := by
  exact smooth_reciprocal_tail_proved A ε hA hε

/-- Page 14 below display 50. The proved composite estimate bounds the
norm of the smooth coefficient tail by its numerical majorant. -/
theorem smooth_tail_norm (n : ℕ) (T Q : ℝ) :
    ‖∑ q ∈ Finset.Ioc ⌊T⌋₊ (4 * smoothModulus Q),
      (smoothWeight q Q : ℂ) * A3 n q‖ ≤
    ∑ q ∈ Finset.Ioc ⌊T⌋₊ (4 * smoothModulus Q),
      smoothWeight q Q * (coefficientMajorant q / (q : ℝ)) := by
  calc
    _ ≤ ∑ q ∈ Finset.Ioc ⌊T⌋₊ (4 * smoothModulus Q),
        ‖(smoothWeight q Q : ℂ) * A3 n q‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q hq
      have hqn : 0 < q := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hq).1
      have hw : 0 ≤ smoothWeight q Q := by unfold smoothWeight; split <;> norm_num
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (coefficient_product_bound n q hqn) hw

/-- Page 14 below display 50. Exact Task403cI438a pointwise tail statement.
CONDITIONAL only on the numerical smooth_reciprocal_tail leaf. -/
theorem smooth_tail_pointwise (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) → ∀ n : ℕ,
      ‖∑ q ∈ Finset.Ioc ⌊y ^ (1 / 3 : ℝ)⌋₊ (4 * smoothModulus Q),
        (smoothWeight q Q : ℂ) * A3 n q‖ ^ 2 ≤
          C / Real.log x ^ A := by
  obtain ⟨C, x0, hC, hx0, hb⟩ := smooth_reciprocal_tail A ε hA hε
  refine ⟨C ^ 2, x0, by positivity, hx0, ?_⟩
  intro x y Q hx hy hyx hQpos hQ n
  have hx2 : 2 ≤ x := hx0.trans hx
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  calc
    _ ≤ (C / Real.log x ^ (A / 2)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        ((smooth_tail_norm n _ Q).trans (hb x y Q hx hy hyx hQpos hQ)) 2
    _ = C ^ 2 / Real.log x ^ A := by
      have hp : (Real.log x ^ (A / 2)) ^ (2 : ℕ) = Real.log x ^ A := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hl.le]
        congr 1
        push_cast
        ring
      rw [div_pow, hp]


end LeanLab.KumchevLiu2007.Task403cI438j


/-! Inlined from Decomp438a.lean, unchanged except for the namespace prefix. -/
/-
Three-square smooth truncation supplies for page 14 display 50.
The finite identity has a clean supply. The smooth estimate is CONDITIONAL.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.KumchevLiu2007.Task403cI438a

open Real Complex Task129b Task129c Task403c Task292c
open scoped BigOperators

/-- LEAF. Page 14 display 50, from page 13 properties i and ii.
The upper support is four times the product of primes at most Q.
The factor at 2 retains the powers 2, 4 and 8. This is finite algebra only. -/
theorem smooth_remainder_identity (n : ℕ) (P Q T : ℝ)
    (hP : 0 < P) (hPQ : P ≤ Q) (hQT : Q ≤ T) :
    (series3 n P - product3 n Q) - tail3 n P T Q =
      -(∑ q ∈ Finset.Ioc ⌊T⌋₊ (4 * smoothModulus Q),
        (smoothWeight q Q : ℂ) * A3 n q) := by
  exact Task403cI438i.smooth_remainder_identity n P Q T hP hPQ hQT

/-- LEAF. Page 14 bound below display 50, using display 47 and Lemma 3.5.
Only the finite smooth coefficient tail remains. There is no P cutoff,
Euler product, subtraction error or average over n in this leaf. -/
theorem smooth_tail_pointwise (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) → ∀ n : ℕ,
      ‖∑ q ∈ Finset.Ioc ⌊y ^ (1 / 3 : ℝ)⌋₊ (4 * smoothModulus Q),
        (smoothWeight q Q : ℂ) * A3 n q‖ ^ 2 ≤
          C / Real.log x ^ A := by
  exact Task403cI438j.smooth_tail_pointwise A ε hA hε

/-- Page 14 display 50. Exact Task403c target from the two smaller leaves.
CONDITIONAL only on Task403cI438j.smooth_reciprocal_tail. -/
theorem truncation_input (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y,
        ‖(series3 n P - product3 n Q) - tail3 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) ≤
          C * (y / Real.log x ^ A) := by
  obtain ⟨C, xs, hC, hxs, hs⟩ := smooth_tail_pointwise A ε hA hε
  obtain ⟨xt, hxt, ht⟩ := Task342d.cutoff_order ε hε
  refine ⟨2 * C, max xs xt, by positivity, hxs.trans (le_max_left _ _), ?_⟩
  intro x y P Q hx hy hyx hP hPQ hQ
  have hxs' : xs ≤ x := (le_max_left _ _).trans hx
  have hxt' : xt ≤ x := (le_max_right _ _).trans hx
  have hx2 : 2 ≤ x := hxs.trans hxs'
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hy1 : 1 ≤ y := (Real.one_le_rpow (by linarith : 1 ≤ x) hε.le).trans hy
  have hQT := ht x y Q hxt' hy hQ
  calc
    _ ≤ ∑ _n ∈ intervalNumbers x y, C / Real.log x ^ A := by
      apply Finset.sum_le_sum
      intro n hn
      rw [smooth_remainder_identity n P Q _ hP hPQ hQT, norm_neg]
      exact hs x y Q hxs' hy hyx (hP.trans_le hPQ) hQ n
    _ = ((intervalNumbers x y).card : ℝ) * (C / Real.log x ^ A) := by simp
    _ ≤ (2 * y) * (C / Real.log x ^ A) :=
      mul_le_mul_of_nonneg_right (Task271a.interval_card_le (by linarith) hy1)
        (by positivity)
    _ = (2 * C) * (y / Real.log x ^ A) := by ring

end LeanLab.KumchevLiu2007.Task403cI438a


/-! Inlined from Decomp438k.lean, unchanged except for the namespace prefix. -/
/-
Numerical diagonal supply from the proved lab Mertens upper bound.
Source page 15 first display. AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.KumchevLiu2007.Task403cI438k

open Real Complex Task129b Task292a
open scoped BigOperators

/-- Page 15 first display. The sixth power of the local product is bounded
by a constant times log x uniformly for positive q at most x to one third. -/
theorem localMajorant_sixth_log_bound :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ (x : ℝ) (q : ℕ),
      x0 ≤ x → 0 < q → (q : ℝ) ≤ x ^ (1 / 3 : ℝ) →
        localMajorant q ^ 6 ≤ C * Real.log x := by
  classical
  refine ⟨Real.exp 504 * ((Nat.factorial 36 : ℕ) : ℝ) * 2,
    max 2 (Real.exp 2), by positivity, le_max_left _ _, ?_⟩
  intro x q hx hq hqx
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  let L := Real.log x
  have hL2 : 2 ≤ L := by
    apply (Real.le_log_iff_exp_le hx0).mpr
    exact (le_max_right _ _).trans hx
  let N : ℕ := ⌈L⌉₊
  have hLN : L ≤ (N : ℝ) := Nat.le_ceil L
  have hN2 : 2 ≤ N := by exact_mod_cast (show (2 : ℝ) ≤ N from hL2.trans hLN)
  have hNupper : (N : ℝ) ≤ 2 * L := by
    have hceil := Nat.ceil_lt_add_one (by linarith : 0 ≤ L)
    dsimp [N]
    linarith
  have hlogq : Real.log (q : ℝ) ≤ L / 3 := by
    have h := Real.log_le_log (by positivity : 0 < (q : ℝ)) hqx
    rw [Real.log_rpow hx0] at h
    dsimp [L]
    linarith
  have hcard : (q.primeFactors.card : ℝ) ≤ 2 * L := by
    have hprod : (2 : ℕ) ^ q.primeFactors.card ≤ q := by
      calc
        _ = ∏ _p ∈ q.primeFactors, (2 : ℕ) := by simp
        _ ≤ ∏ p ∈ q.primeFactors, p := Finset.prod_le_prod
          (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
        _ ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
    have hcast : (2 : ℝ) ^ q.primeFactors.card ≤ (q : ℝ) := by exact_mod_cast hprod
    have hl := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ q.primeFactors.card) hcast
    rw [Real.log_pow] at hl
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith
  let S := q.primeFactors.filter (fun p => p ≤ N)
  let T := q.primeFactors.filter (fun p => ¬ p ≤ N)
  have hsmall : (∑ p ∈ S, 1 / (p : ℝ)) ≤ Real.log (Real.log (N : ℝ)) + 12 := by
    have hsub : S ⊆ (Finset.Icc 1 N).filter Nat.Prime := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpq, hpN⟩
      have hprime := Nat.prime_of_mem_primeFactors hpq
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hprime.one_le, hpN⟩, hprime⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp hnot => by positivity)).trans
      (LeanLab.PNTSieve.Mertens.sum_inv_primes_le N hN2)
  have hlarge : (∑ p ∈ T, 1 / (p : ℝ)) ≤ 2 := by
    calc
      _ ≤ ∑ _p ∈ T, 1 / L := by
        apply Finset.sum_le_sum
        intro p hp
        have hpN : N < p := Nat.lt_of_not_ge (Finset.mem_filter.mp hp).2
        exact one_div_le_one_div_of_le (by linarith) (hLN.trans (by exact_mod_cast hpN.le))
      _ = (T.card : ℝ) / L := by simp [div_eq_mul_inv]
      _ ≤ (q.primeFactors.card : ℝ) / L := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun p => ¬ p ≤ N) q.primeFactors)
      _ ≤ 2 := (div_le_iff₀ (by linarith : 0 < L)).mpr (by linarith)
  have hsum : (∑ p ∈ q.primeFactors, 1 / (p : ℝ)) ≤ Real.log (Real.log (N : ℝ)) + 14 := by
    have he := Finset.sum_filter_add_sum_filter_not q.primeFactors (fun p => p ≤ N)
      (fun p => 1 / (p : ℝ))
    change (∑ p ∈ S, 1 / (p : ℝ)) + (∑ p ∈ T, 1 / (p : ℝ)) = _ at he
    linarith
  have hMpos : 0 < localMajorant q := by
    unfold localMajorant
    exact Finset.prod_pos (fun p hp => by positivity)
  have hlogM : Real.log (localMajorant q) ≤ 6 * (Real.log (Real.log (N : ℝ)) + 14) := by
    rw [localMajorant, Real.log_prod (fun p hp => by positivity)]
    have ht : ∀ p ∈ q.primeFactors, Real.log (1 + 6 / (p : ℝ)) ≤ 6 * (1 / (p : ℝ)) := by
      intro p hp
      have hb := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 6 / (p : ℝ))
      convert hb using 1 <;> ring
    exact (Finset.sum_le_sum ht).trans (by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hsum (by norm_num))
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hM : localMajorant q ^ 6 ≤ Real.exp 504 * (Real.log (N : ℝ)) ^ 36 := by
    have hl : Real.log (localMajorant q ^ 6) ≤ 36 * Real.log (Real.log (N : ℝ)) + 504 := by
      rw [Real.log_pow]
      have hh := mul_le_mul_of_nonneg_left hlogM (by norm_num : (0 : ℝ) ≤ 6)
      convert hh using 1 <;> ring
    have hh := (Real.log_le_iff_le_exp (by positivity : 0 < localMajorant q ^ 6)).mp hl
    have he : Real.exp (36 * Real.log (Real.log (N : ℝ)) + 504) =
        Real.exp 504 * (Real.log (N : ℝ)) ^ 36 := by
      rw [Real.exp_add, show (36 : ℝ) = ((36 : ℕ) : ℝ) by norm_num,
        Real.exp_nat_mul, Real.exp_log hlogN]
      ring
    exact hh.trans_eq he
  have hfac : (Real.log (N : ℝ)) ^ 36 ≤ ((Nat.factorial 36 : ℕ) : ℝ) * (N : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (Real.log (N : ℝ)) hlogN.le 36
    rw [Real.exp_log (by exact_mod_cast (show 0 < N by omega)),
      div_le_iff₀ (by positivity : 0 < ((Nat.factorial 36 : ℕ) : ℝ))] at h
    nlinarith
  calc
    _ ≤ Real.exp 504 * (((Nat.factorial 36 : ℕ) : ℝ) * (N : ℝ)) :=
      hM.trans (mul_le_mul_of_nonneg_left hfac (by positivity))
    _ ≤ Real.exp 504 * (((Nat.factorial 36 : ℕ) : ℝ) * (2 * L)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hNupper (by positivity)) (by positivity)
    _ = _ := by dsimp [L]; ring

/-- Page 15 first display. Exact Task403cI438b numerical reciprocal square tail
supply from the sixth power product bound and the proved real cutoff tail. -/
theorem majorant_square_tail :
    ∃ K x0 : ℝ, 0 < K ∧ 2 ≤ x0 ∧ ∀ x P : ℝ,
      x0 ≤ x → 0 < P →
      (∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊x ^ (1 / 3 : ℝ)⌋₊,
        localMajorant q ^ 6 / (q : ℝ) ^ 2) ≤
          K * (Real.log x / P) := by
  obtain ⟨C, x0, hC, hx0, hb⟩ := localMajorant_sixth_log_bound
  refine ⟨2 * C, x0, by positivity, hx0, ?_⟩
  intro x P hx hP
  have hx2 : 2 ≤ x := hx0.trans hx
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  calc
    _ ≤ ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊x ^ (1 / 3 : ℝ)⌋₊,
        C * Real.log x / (q : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      have hqn : 0 < q := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hq).1
      have hqx : (q : ℝ) ≤ x ^ (1 / 3 : ℝ) :=
        (Nat.cast_le.mpr (Finset.mem_Ioc.mp hq).2).trans (Nat.floor_le (by positivity))
      exact div_le_div_of_nonneg_right (hb x q hx hqn hqx) (by positivity)
    _ = C * Real.log x * ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊x ^ (1 / 3 : ℝ)⌋₊,
        1 / (q : ℝ) ^ 2 := by simp [Finset.mul_sum, div_eq_mul_inv]
    _ ≤ C * Real.log x * (2 / P) :=
      mul_le_mul_of_nonneg_left (Task292a.reciprocal_square_tail P _ hP) (by positivity)
    _ = (2 * C) * (Real.log x / P) := by ring


end LeanLab.KumchevLiu2007.Task403cI438k


/-! Inlined from Decomp438l.lean, unchanged except for the namespace prefix. -/
/-
Full period supply for the three-square diagonal mean square.
Source page 15 first display and Schwarz page 83 display 2.11.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.KumchevLiu2007.Task403cI438l

open Real Complex Task129b Task129c Task292a Task403cI438g
open scoped BigOperators

/-- Page 15 first display, derived normalization. Multiply the complete
period square sum by the modulus to obtain a multiplicative local mass. -/
noncomputable def periodMass (q : ℕ) : ℝ :=
  (q : ℝ) * ∑ n ∈ Finset.range q, ‖A3 n q‖ ^ 2

/-- Page 13 display 45, finite residue bookkeeping for the period average. -/
theorem residue_sum_eq_range (q : ℕ) [NeZero q] (f : ℕ → ℝ) :
    (∑ n : ZMod q, f n.val) = ∑ n ∈ Finset.range q, f n := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q => exact Fin.sum_univ_eq_sum_range f (q + 1)

/-- Page 15 first display, derived Chinese remainder step from
page 13 property i. -/
theorem periodMass_coprime_mul (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) :
    periodMass (a * b) = periodMass a * periodMass b := by
  classical
  letI : NeZero a := ⟨by omega⟩
  letI : NeZero b := ⟨by omega⟩
  letI : NeZero (a * b) := ⟨by positivity⟩
  have hval (q : ℕ) [NeZero q] (z : ZMod (a * b)) :
      A3 z.val q = A3 (ZMod.cast z : ZMod q).val q := by
    rw [ZMod.cast_eq_val, ZMod.val_natCast]
    exact ((Task403a.A3_periodic q).map_mod_nat z.val).symm
  have hs : (∑ n : ZMod (a * b), ‖A3 n.val (a * b)‖ ^ 2) =
      (∑ n : ZMod a, ‖A3 n.val a‖ ^ 2) * (∑ n : ZMod b, ‖A3 n.val b‖ ^ 2) := by
    calc
      _ = ∑ z : ZMod (a * b),
          (fun w : ZMod a × ZMod b => ‖A3 w.1.val a‖ ^ 2 * ‖A3 w.2.val b‖ ^ 2)
            (ZMod.chineseRemainder hab z) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [Task403cI438e.A3_coprime_mul _ a b hab, norm_mul, mul_pow, hval a z, hval b z]
        have hc : ZMod.chineseRemainder hab z =
            ((ZMod.cast z : ZMod a), (ZMod.cast z : ZMod b)) := by
          calc
            _ = ZMod.chineseRemainder hab (z.val : ZMod (a * b)) := by
              rw [ZMod.natCast_zmod_val]
            _ = ((z.val : ZMod a), (z.val : ZMod b)) := by
              rw [map_natCast]
              rfl
            _ = _ := by simp only [ZMod.cast_eq_val]
        rw [hc]
      _ = ∑ w : ZMod a × ZMod b, ‖A3 w.1.val a‖ ^ 2 * ‖A3 w.2.val b‖ ^ 2 :=
        Equiv.sum_comp (ZMod.chineseRemainder hab).toEquiv
          (fun w : ZMod a × ZMod b => ‖A3 w.1.val a‖ ^ 2 * ‖A3 w.2.val b‖ ^ 2)
      _ = _ := by
        rw [Fintype.sum_prod_type, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mul_sum]
  rw [residue_sum_eq_range (a * b) (fun n => ‖A3 n (a * b)‖ ^ 2),
    residue_sum_eq_range a (fun n => ‖A3 n a‖ ^ 2),
    residue_sum_eq_range b (fun n => ‖A3 n b‖ ^ 2)] at hs
  simp only [periodMass, Nat.cast_mul]
  rw [hs]
  ring

/-- Page 13 display 45. The normalized modulus one mass equals one. -/
theorem periodMass_one : periodMass 1 = 1 := by
  simp [periodMass, Task403cI438d.A3_one]

/-- Page 13 property ii. Every vanishing coefficient gives zero mass. -/
theorem periodMass_prime_power_zero (p k : ℕ) (hp : p.Prime)
    (hk : (p ≠ 2 ∧ 2 ≤ k) ∨ (p = 2 ∧ 4 ≤ k)) :
    periodMass (p ^ k) = 0 := by
  simp [periodMass, Task403cI438f.A3_prime_power_vanish _ p k hp hk]

/-- Page 13 property ii and page 15 first display. The three retained
powers of two have normalized mass at most 4096. -/
theorem periodMass_small_dyadic (k : ℕ) (hk : 1 ≤ k) (hk3 : k ≤ 3) :
    periodMass (2 ^ k) ≤ 4096 := by
  have hq : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  have hsum : (∑ n ∈ Finset.range (2 ^ k), ‖A3 n (2 ^ k)‖ ^ 2) ≤
      ((2 ^ k : ℕ) : ℝ) * (64 / ((2 ^ k : ℕ) : ℝ)) ^ 2 := by
    calc
      _ ≤ ∑ _n ∈ Finset.range (2 ^ k), (64 / ((2 ^ k : ℕ) : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        exact pow_le_pow_left₀ (norm_nonneg _)
          (Task403cI438d.A3_small_dyadic_bound n k hk hk3) 2
      _ = _ := by simp
  unfold periodMass
  calc
    _ ≤ ((2 ^ k : ℕ) : ℝ) *
        (((2 ^ k : ℕ) : ℝ) * (64 / ((2 ^ k : ℕ) : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum hq.le
    _ = 4096 := by field_simp [ne_of_gt hq]; ring

/-- Page 13 display 45 and page 15 first display. Finite Parseval identity
for the standard additive character. -/
theorem character_parseval (q : ℕ) [NeZero q] (b : ZMod q → ℂ) :
    (∑ n : ZMod q, ‖∑ a : ZMod q, b a * ZMod.stdAddChar (N := q) (-(a * n))‖ ^ 2) =
      (q : ℝ) * ∑ a : ZMod q, ‖b a‖ ^ 2 := by
  classical
  have hstar (z : ZMod q) : (starRingEnd ℂ) (ZMod.stdAddChar (N := q) z) =
      ZMod.stdAddChar (N := q) (-z) := by
    rw [AddChar.starComp_apply (by rw [ZMod.ringChar_zmod_n]; exact NeZero.pos q),
      AddChar.inv_apply]
  have he (a c n : ZMod q) :
      (b a * ZMod.stdAddChar (N := q) (-(a * n))) *
        (starRingEnd ℂ) (b c * ZMod.stdAddChar (N := q) (-(c * n))) =
      (b a * (starRingEnd ℂ) (b c)) * ZMod.stdAddChar (N := q) (n * (c - a)) := by
    rw [map_mul, hstar, neg_neg]
    have halg : n * (c - a) = -(a * n) + c * n := by ring
    rw [halg, AddChar.map_add_eq_mul]
    ring
  have hn (n : ZMod q) :
      ‖∑ a : ZMod q, b a * ZMod.stdAddChar (N := q) (-(a * n))‖ ^ 2 =
      (∑ a : ZMod q, ∑ c : ZMod q,
        (b a * (starRingEnd ℂ) (b c)) * ZMod.stdAddChar (N := q) (n * (c - a))).re := by
    have h := congrArg Complex.re (Complex.mul_conj
      (∑ a : ZMod q, b a * ZMod.stdAddChar (N := q) (-(a * n))))
    simp only [Complex.ofReal_re, Complex.normSq_eq_norm_sq] at h
    rw [← h]
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum, he]
    rw [Finset.sum_comm]
  simp_rw [hn]
  rw [← Complex.re_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 1; arg 2; ext a; rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q), sub_eq_zero]
  push_cast
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, ZMod.card]
  simp only [Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Page 13 display 45 and page 15 first display. The complete coefficient
mean square over residues is exactly q divided by the sixth power of the
totient times the sixth moment of the reduced quadratic sums. -/
theorem A3_period_square_identity (q : ℕ) [NeZero q] :
    (∑ n : ZMod q, ‖A3 n.val q‖ ^ 2) =
      (q : ℝ) / (Nat.totient q : ℝ) ^ 6 *
        ∑ a ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
          ‖∑ x ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
            ZMod.stdAddChar (N := q) (a * x * x)‖ ^ 6 := by
  classical
  let F : ZMod q → ℂ := fun a =>
    ∑ x ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
      ZMod.stdAddChar (N := q) (a * x * x)
  let b : ZMod q → ℂ := fun a =>
    (if IsUnit a then F a ^ 3 else 0) / (Nat.totient q : ℂ) ^ 3
  have ha (n : ZMod q) : A3 n.val q =
      ∑ a : ZMod q, b a * ZMod.stdAddChar (N := q) (-(a * n)) := by
    rw [Task342h.A3_zmod_formula, ZMod.natCast_zmod_val, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hunit : IsUnit a <;> simp [b, F, hunit] <;> ring
  have hb (a : ZMod q) : ‖b a‖ ^ 2 =
      if IsUnit a then ‖F a‖ ^ 6 / (Nat.totient q : ℝ) ^ 6 else 0 := by
    by_cases hunit : IsUnit a
    · simp only [b, hunit, ite_true, norm_div, norm_pow, Complex.norm_natCast, div_pow, ← pow_mul]
    · simp [b, hunit]
  simp_rw [ha]
  rw [character_parseval]
  simp_rw [hb]
  rw [← Finset.sum_filter]
  change (q : ℝ) * (∑ a ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
    ‖F a‖ ^ 6 / (Nat.totient q : ℝ) ^ 6) = _
  rw [← Finset.sum_div]
  dsimp [F]
  ring

/-- Page 15 first display through page 13 display 45, derived local identity.
The sixth moment depends only on the squared real part of the quadratic Gauss sum. -/
theorem sixth_moment_identity (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (∑ a ∈ (Finset.univ : Finset (ZMod p)).filter IsUnit,
      ‖∑ x ∈ (Finset.univ : Finset (ZMod p)).filter IsUnit,
        ZMod.stdAddChar (N := p) (a * x * x)‖ ^ 6) =
      ((p : ℝ) - 1) * (((p : ℝ) + 1) ^ 3 + 12 * ((p : ℝ) + 1) *
        (gaussSum (quadraticC p) (ZMod.stdAddChar (N := p))).re ^ 2) := by
  classical
  let G := gaussSum (quadraticC p) (ZMod.stdAddChar (N := p))
  let S := (Finset.univ : Finset (ZMod p)).erase 0
  have hset : (Finset.univ : Finset (ZMod p)).filter IsUnit = S := by
    ext a
    simp [S, isUnit_iff_ne_zero]
  have hG : ‖G‖ ^ 2 = (p : ℝ) := by
    simpa only [norm_pow] using quadratic_gauss_sq_norm p hp
  have hGre : G.re ^ 2 + G.im ^ 2 = (p : ℝ) := by
    simpa only [Complex.sq_norm, Complex.normSq_apply, ← sq] using hG
  have hterm (a : ZMod p) (ha : a ∈ S) :
      ‖quadraticC p a * G - 1‖ ^ 6 =
      ((p : ℝ) + 1) ^ 3 + 12 * ((p : ℝ) + 1) * G.re ^ 2 -
        (6 * ((p : ℝ) + 1) ^ 2 * G.re + 8 * G.re ^ 3) * (quadraticC p a).re := by
    have ha0 := Finset.ne_of_mem_erase ha
    have hs := quadraticC_sq p a ha0
    have hc : quadraticC p a = 1 ∨ quadraticC p a = -1 := sq_eq_one_iff.mp hs
    rcases hc with hc | hc
    · rw [hc, one_mul, Complex.one_re]
      have hn : ‖G - 1‖ ^ 2 = (p : ℝ) + 1 - 2 * G.re := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
        nlinarith [hGre]
      calc
        _ = (‖G - 1‖ ^ 2) ^ 3 := by ring
        _ = _ := by rw [hn]; ring
    · rw [hc, neg_one_mul, Complex.neg_re, Complex.one_re]
      have hn : ‖-G - 1‖ ^ 2 = (p : ℝ) + 1 + 2 * G.re := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
          Complex.one_re, Complex.one_im, sub_zero]
        nlinarith [hGre]
      calc
        _ = (‖-G - 1‖ ^ 2) ^ 3 := by ring
        _ = _ := by rw [hn]; ring
  have hsum : (∑ a ∈ S, (quadraticC p a).re) = 0 := by
    have hχ := MulChar.sum_eq_zero_of_ne_one (quadraticC_properties p hp).1
    have h0 : quadraticC p (0 : ZMod p) = 0 := by
      simp [quadraticC, MulChar.ringHomComp_apply]
    have he := Finset.sum_erase_add (Finset.univ : Finset (ZMod p))
      (fun a => quadraticC p a) (Finset.mem_univ 0)
    rw [h0, add_zero, hχ] at he
    have hr := congrArg Complex.re he
    simpa only [Complex.re_sum, Complex.zero_re, S] using hr
  rw [hset]
  calc
    _ = ∑ a ∈ S, ‖quadraticC p a * G - 1‖ ^ 6 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← hset, reduced_quadratic_sum p hp a (Finset.ne_of_mem_erase ha)]
    _ = ∑ a ∈ S, (((p : ℝ) + 1) ^ 3 + 12 * ((p : ℝ) + 1) * G.re ^ 2 -
        (6 * ((p : ℝ) + 1) ^ 2 * G.re + 8 * G.re ^ 3) * (quadraticC p a).re) :=
      Finset.sum_congr rfl hterm
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_zero, sub_zero, Finset.sum_const]
      have hcard : (S.card : ℝ) = (p : ℝ) - 1 := by
        simp only [S, Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)),
          Finset.card_univ, ZMod.card, Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one]
      rw [nsmul_eq_mul, hcard]

/-- Page 15 first display, derived local sixth moment bound. -/
theorem sixth_moment_polynomial (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (∑ a ∈ (Finset.univ : Finset (ZMod p)).filter IsUnit,
      ‖∑ x ∈ (Finset.univ : Finset (ZMod p)).filter IsUnit,
        ZMod.stdAddChar (N := p) (a * x * x)‖ ^ 6) ≤
      ((p : ℝ) - 1) * ((p : ℝ) ^ 3 + 15 * (p : ℝ) ^ 2 + 15 * (p : ℝ) + 1) := by
  rw [sixth_moment_identity p hp]
  let G := gaussSum (quadraticC p) (ZMod.stdAddChar (N := p))
  have hG : ‖G‖ ^ 2 = (p : ℝ) := by
    simpa only [norm_pow] using quadratic_gauss_sq_norm p hp
  have hGr : G.re ^ 2 ≤ (p : ℝ) := by
    nlinarith [Complex.sq_norm_sub_sq_re G, sq_nonneg G.im]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  calc
    _ ≤ ((p : ℝ) - 1) * (((p : ℝ) + 1) ^ 3 + 12 * ((p : ℝ) + 1) * (p : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      apply add_le_add_right
      exact mul_le_mul_of_nonneg_left hGr (by positivity)
    _ = _ := by ring

/-- Page 15 first display, derived numerical local factor comparison. -/
theorem local_moment_numerical (x : ℝ) (hx : 3 ≤ x) :
    (x - 1) * (x ^ 3 + 15 * x ^ 2 + 15 * x + 1) ≤
      (x - 1) ^ 6 / x ^ 2 * (1 + 6 / x) ^ 6 := by
  have hx0 : 0 < x := by linarith
  have ht : 0 ≤ x - 3 := by linarith
  have hpoly : x ^ 8 * (x ^ 3 + 15 * x ^ 2 + 15 * x + 1) ≤
      (x - 1) ^ 5 * (x + 6) ^ 6 := by
    apply sub_nonneg.mp
    convert (show 0 ≤ 16 * (x - 3) ^ 10 + 835 * (x - 3) ^ 9 +
      18034 * (x - 3) ^ 8 + 217001 * (x - 3) ^ 7 + 1621508 * (x - 3) ^ 6 +
      7866369 * (x - 3) ^ 5 + 25081650 * (x - 3) ^ 4 + 51989607 * (x - 3) ^ 3 +
      67295448 * (x - 3) ^ 2 + 49347468 * (x - 3) + 15641424 by positivity) using 1 <;> ring
  have he : (x - 1) ^ 6 / x ^ 2 * (1 + 6 / x) ^ 6 =
      (x - 1) ^ 6 * (x + 6) ^ 6 / x ^ 8 := by
    field_simp [ne_of_gt hx0]
    <;> ring
  rw [he, le_div_iff₀ (pow_pos hx0 8)]
  calc
    _ = (x - 1) * (x ^ 8 * (x ^ 3 + 15 * x ^ 2 + 15 * x + 1)) := by ring
    _ ≤ (x - 1) * ((x - 1) ^ 5 * (x + 6) ^ 6) :=
      mul_le_mul_of_nonneg_left hpoly (by linarith)
    _ = _ := by ring

/-- Page 15 first display, exact local sixth moment supply. -/
theorem odd_prime_sixth_moment (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    (∑ a ∈ (Finset.univ : Finset (ZMod p)).filter IsUnit,
      ‖∑ x ∈ (Finset.univ : Finset (ZMod p)).filter IsUnit,
        ZMod.stdAddChar (N := p) (a * x * x)‖ ^ 6) ≤
      (Nat.totient p : ℝ) ^ 6 / (p : ℝ) ^ 2 * (1 + 6 / (p : ℝ)) ^ 6 := by
  have hp2 : p ≠ 2 := by omega
  have hb := (sixth_moment_polynomial p hp2).trans
    (local_moment_numerical (p : ℝ) (by exact_mod_cast hp))
  simpa only [Nat.totient_prime (Fact.out : p.Prime),
    Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one] using hb

/-- Page 15 first display. Parseval converts the local sixth moment
bound into the normalized odd prime mass bound. -/
theorem periodMass_odd_prime (p : ℕ) (hp : p.Prime) (hodd : 2 < p) :
    periodMass p ≤ (1 + 6 / (p : ℝ)) ^ 6 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have ht : (0 : ℝ) < Nat.totient p := by exact_mod_cast Nat.totient_pos.mpr hp.pos
  have hi := A3_period_square_identity p
  rw [residue_sum_eq_range p (fun n => ‖A3 n p‖ ^ 2)] at hi
  have hm := odd_prime_sixth_moment p hodd
  unfold periodMass
  rw [hi]
  calc
    _ ≤ (p : ℝ) * ((p : ℝ) / (Nat.totient p : ℝ) ^ 6 *
      ((Nat.totient p : ℝ) ^ 6 / (p : ℝ) ^ 2 * (1 + 6 / (p : ℝ)) ^ 6)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm (by positivity)) hp0.le
    _ = _ := by field_simp [ne_of_gt hp0, ne_of_gt ht]

/-- Page 15 first display. The normalized prime power estimate retains
all three even prime factors. -/
theorem periodMass_prime_power (p k : ℕ) (hp : p.Prime) :
    periodMass (p ^ k) ≤ localMajorant (p ^ k) ^ 6 := by
  by_cases hk : k = 0
  · subst k
    simp [periodMass_one, localMajorant]
  have hM : localMajorant (p ^ k) = 1 + 6 / (p : ℝ) := by
    simp [localMajorant, Nat.primeFactors_prime_pow hk hp]
  rw [hM]
  by_cases hp2 : p = 2
  · subst p
    by_cases hk3 : k ≤ 3
    · norm_num
      exact periodMass_small_dyadic k (by omega) hk3
    · rw [periodMass_prime_power_zero 2 k hp (Or.inr ⟨rfl, by omega⟩)]
      positivity
  · by_cases hk1 : k = 1
    · subst k
      simpa using periodMass_odd_prime p hp (by have := hp.two_le; omega)
    · rw [periodMass_prime_power_zero p k hp (Or.inl ⟨hp2, by omega⟩)]
      positivity

/-- Page 15 first display. The normalized mass is bounded by the sixth
power of the local prime product. -/
theorem periodMass_bound (q : ℕ) (hq : 0 < q) :
    periodMass q ≤ localMajorant q ^ 6 := by
  classical
  induction q using Nat.recOnPrimeCoprime with
  | zero => omega
  | prime_pow p k hp => exact periodMass_prime_power p k hp
  | coprime a b ha hb hab ih_a ih_b =>
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have hM : localMajorant (a * b) = localMajorant a * localMajorant b := by
      simp only [localMajorant, Nat.primeFactors_mul ha0 hb0,
        Finset.prod_union hab.disjoint_primeFactors]
    rw [periodMass_coprime_mul a b (by omega) (by omega) hab, hM, mul_pow]
    apply mul_le_mul (ih_a (by omega)) (ih_b (by omega))
    · exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun n hn => sq_nonneg _))
    · positivity

/-- LEAF. Page 15 first display, using the character definition on page 13
and Schwarz page 83 display 2.11. This is only a complete period average
at one modulus. There is no interval, P, Q, x or y variable.
The even prime powers through 8 are included. -/
theorem complete_period_square :
    ∃ K : ℝ, 0 < K ∧ ∀ q : ℕ, 0 < q →
      (∑ n ∈ Finset.range q, ‖A3 n q‖ ^ 2) ≤
        K * (localMajorant q ^ 6 / (q : ℝ)) := by
  refine ⟨1, by norm_num, ?_⟩
  intro q hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rw [one_mul, le_div_iff₀ hq0]
  simpa only [periodMass, mul_comm] using periodMass_bound q hq

/-- Page 15 first display. A nonnegative periodic function summed over
an interval of length at least its period is bounded by six times the
length divided by the period times its complete period sum. -/
theorem nonnegative_periodic_interval (v : ℕ → ℝ) (q : ℕ) (hq : 0 < q)
    (hp : Function.Periodic v q) (hv : ∀ n, 0 ≤ v n)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 1 ≤ y) (hqy : (q : ℝ) ≤ y) :
    (∑ n ∈ intervalNumbers x y, v n) ≤
      6 * y / (q : ℝ) * (∑ n ∈ Finset.range q, v n) := by
  classical
  let S := ∑ n ∈ Finset.range q, v n
  let μ := S / (q : ℝ)
  let g : ℕ → ℂ := fun n => ((v n - μ : ℝ) : ℂ)
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hS : 0 ≤ S := Finset.sum_nonneg (fun n hn => hv n)
  have hμ : 0 ≤ μ := div_nonneg hS (by positivity)
  have hqμ : (q : ℝ) * μ = S := by dsimp [μ]; field_simp
  have hgper : Function.Periodic g q := by intro n; simp [g, hp n]
  have hgzero : (∑ n ∈ Finset.range q, g n) = 0 := by
    have he : (∑ n ∈ Finset.range q, g n) = ((S - (q : ℝ) * μ : ℝ) : ℂ) := by
      simp [g, S, Finset.sum_sub_distrib]
    rw [he, hqμ, sub_self, Complex.ofReal_zero]
  have hgperiod : (∑ n ∈ Finset.range q, ‖g n‖) ≤ 2 * S := by
    calc
      _ ≤ ∑ n ∈ Finset.range q, (v n + μ) := by
        apply Finset.sum_le_sum
        intro n hn
        calc
          _ = |v n - μ| := by
            change ‖((v n - μ : ℝ) : ℂ)‖ = _
            rw [Complex.norm_real, Real.norm_eq_abs]
          _ ≤ |v n| + |μ| := abs_sub _ _
          _ = _ := by rw [abs_of_nonneg (hv n), abs_of_nonneg hμ]
      _ = 2 * S := by simp [Finset.sum_add_distrib, ← hqμ, S]; ring
  have hi : ‖∑ n ∈ intervalNumbers x y, g n‖ ≤ 4 * S := by
    have h := periodic_zero_mean_interval g hq hgper hgzero
      (Order.succ ⌊x⌋₊) (Order.succ ⌊x + y⌋₊)
    have h' : ‖∑ n ∈ intervalNumbers x y, g n‖ ≤ 2 * ∑ n ∈ Finset.range q, ‖g n‖ := by
      simpa only [intervalNumbers, ← Finset.Ico_succ_succ_eq_Ioc] using h
    exact h'.trans (by linarith)
  have hgsum : (∑ n ∈ intervalNumbers x y, g n) =
      (((∑ n ∈ intervalNumbers x y, v n) - ((intervalNumbers x y).card : ℝ) * μ : ℝ) : ℂ) := by
    simp [g, Finset.sum_sub_distrib]
  rw [hgsum, Complex.norm_real, Real.norm_eq_abs] at hi
  have hcard := Task271a.interval_card_le hx hy
  have hmain : ((intervalNumbers x y).card : ℝ) * μ ≤ 2 * y * μ :=
    mul_le_mul_of_nonneg_right hcard hμ
  have hSmain : S ≤ y * μ := by nlinarith
  have herr := le_abs_self ((∑ n ∈ intervalNumbers x y, v n) - ((intervalNumbers x y).card : ℝ) * μ)
  have hbound : (∑ n ∈ intervalNumbers x y, v n) ≤ 6 * y * μ := by nlinarith
  have heq : 6 * y * μ = 6 * y / (q : ℝ) * S := by dsimp [μ]; ring
  exact hbound.trans_eq heq

/-- Page 15 first display. Exact Task403cI438b single modulus interval supply.
CONDITIONAL only on complete_period_square. -/
theorem coefficient_interval_square :
    ∃ K : ℝ, 0 < K ∧ ∀ x y : ℝ, ∀ q : ℕ,
      0 ≤ x → 1 ≤ y → 0 < q → (q : ℝ) ^ 3 ≤ y →
      (∑ n ∈ intervalNumbers x y, ‖A3 n q‖ ^ 2) ≤
        K * y * (localMajorant q ^ 6 / (q : ℝ) ^ 2) := by
  obtain ⟨K, hK, hb⟩ := complete_period_square
  refine ⟨6 * K, by positivity, ?_⟩
  intro x y q hx hy hq hqy
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqle : (q : ℝ) ≤ y := by
    have hpos : 0 ≤ (q : ℝ) * ((q : ℝ) - 1) * ((q : ℝ) + 1) := by positivity
    nlinarith
  have hper : Function.Periodic (fun n => ‖A3 n q‖ ^ 2) q := by
    intro n
    change ‖A3 (n + q) q‖ ^ 2 = ‖A3 n q‖ ^ 2
    have he : A3 (n + q) q = A3 n q := Task403a.A3_periodic q n
    rw [he]
  calc
    _ ≤ 6 * y / (q : ℝ) * (∑ n ∈ Finset.range q, ‖A3 n q‖ ^ 2) :=
      nonnegative_periodic_interval _ q hq hper (fun n => sq_nonneg _) x y hx hy hqle
    _ ≤ 6 * y / (q : ℝ) * (K * (localMajorant q ^ 6 / (q : ℝ))) :=
      mul_le_mul_of_nonneg_left (hb q hq) (by positivity)
    _ = (6 * K) * y * (localMajorant q ^ 6 / (q : ℝ) ^ 2) := by ring


end LeanLab.KumchevLiu2007.Task403cI438l


/-! Inlined from Decomp438b.lean, unchanged except for the namespace prefix. -/
/-
Single modulus and numerical supplies for the three-square diagonal.
Source page 15 first display. The numerical leaf is proved. The period coefficient estimate remains OPEN.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.KumchevLiu2007.Task403cI438b

open Real Complex Task129b Task129c Task292a
open scoped BigOperators

/-- LEAF. Page 15 first display, from the coefficient definition on page 13
and Schwarz page 83 display 2.11. Only one modulus occurs. Averaging its
squared coefficient retains the local root count cancellation.
The condition q cubed at most y supplies enough complete periods. -/
theorem coefficient_interval_square :
    ∃ K : ℝ, 0 < K ∧ ∀ x y : ℝ, ∀ q : ℕ,
      0 ≤ x → 1 ≤ y → 0 < q → (q : ℝ) ^ 3 ≤ y →
      (∑ n ∈ intervalNumbers x y, ‖A3 n q‖ ^ 2) ≤
        K * y * (localMajorant q ^ 6 / (q : ℝ) ^ 2) := by
  exact Task403cI438l.coefficient_interval_square

/-- LEAF. Page 15 first display, numerical reciprocal square tail.
No A3 coefficient, smooth weight or n variable occurs here.
The local product has only factors 1 plus 6 divided by p. -/
theorem majorant_square_tail :
    ∃ K x0 : ℝ, 0 < K ∧ 2 ≤ x0 ∧ ∀ x P : ℝ,
      x0 ≤ x → 0 < P →
      (∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊x ^ (1 / 3 : ℝ)⌋₊,
        localMajorant q ^ 6 / (q : ℝ) ^ 2) ≤
          K * (Real.log x / P) := by
  exact Task403cI438k.majorant_square_tail

/-- Page 15 first display. Exact Task403c diagonal target.
CONDITIONAL only on Task403cI438l.complete_period_square. -/
theorem diagonal_bound :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → 1 ≤ y → y ≤ x → 0 < P →
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ‖-(smoothWeight q Q : ℂ) * A3 n q‖ ^ 2) ≤
        C * (y / P * Real.log x) := by
  obtain ⟨K, hK, hk⟩ := coefficient_interval_square
  obtain ⟨L, x0, hL, hx0, hl⟩ := majorant_square_tail
  refine ⟨K * L, x0, by positivity, hx0, ?_⟩
  intro x y P Q hx hy hyx hP
  have hx2 : 2 ≤ x := hx0.trans hx
  have hxy : y ^ (1 / 3 : ℝ) ≤ x ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow (by linarith) hyx (by norm_num)
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
        K * y * (localMajorant q ^ 6 / (q : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqn : 0 < q := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hq).1
      have hqy : (q : ℝ) ≤ y ^ (1 / 3 : ℝ) :=
        (Nat.cast_le.mpr (Finset.mem_Ioc.mp hq).2).trans (Nat.floor_le (by positivity))
      have hcube : (q : ℝ) ^ 3 ≤ y := by
        calc
          _ ≤ (y ^ (1 / 3 : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) hqy 3
          _ = y := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ y)]
            norm_num
      calc
        _ ≤ ∑ n ∈ intervalNumbers x y, ‖A3 n q‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro n hn
          apply pow_le_pow_left₀ (norm_nonneg _)
          rw [norm_mul, norm_neg]
          exact mul_le_of_le_one_left (norm_nonneg _)
            (Task271b.smoothWeight_norm_le_one q Q)
        _ ≤ _ := hk x y q (by linarith) hy hqn hcube
    _ = K * y * ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
        localMajorant q ^ 6 / (q : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ K * y * ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊x ^ (1 / 3 : ℝ)⌋₊,
        localMajorant q ^ 6 / (q : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.Ioc_subset_Ioc le_rfl (Nat.floor_mono hxy)
      · intro q hq hnot
        positivity
    _ ≤ K * y * (L * (Real.log x / P)) :=
      mul_le_mul_of_nonneg_left (hl x P hx hP) (by positivity)
    _ = K * L * (y / P * Real.log x) := by ring

end LeanLab.KumchevLiu2007.Task403cI438b

namespace LeanLab.KumchevLiu2007.Task403c

open Real Complex Task129b Task129c
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- LEAF. Page 14 display 50 and the smooth tail bound immediately below it,
for j equal to three. Only the error after removing the finite tail remains.
The coefficient bound in display 47 and Lemma 3.5 are the analytic inputs.
PROVED from the inlined copy of Task438a.truncation_input. -/
theorem truncation_input (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y,
        ‖(series3 n P - product3 n Q) - tail3 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) ≤
          C * (y / Real.log x ^ A) := by
  exact Task403cI438a.truncation_input A ε hA hε

/-- LEAF. Page 15 first display for j equal to three. This is only the
sum over equal moduli, using display 47 and the reciprocal square tail.
PROVED from the inlined copy of Task438b.diagonal_bound. -/
theorem diagonal_bound :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → 1 ≤ y → y ≤ x → 0 < P →
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ‖-(smoothWeight q Q : ℂ) * A3 n q‖ ^ 2) ≤
        C * (y / P * Real.log x) := by
  exact Task403cI438b.diagonal_bound

/-- LEAF. Page 15 second and third displays for j equal to three.
Only distinct moduli occur. Task403b proves the incomplete period step.
The remaining coefficient estimate and modulus summation stay OPEN. -/
theorem off_diagonal_power_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x y P Q : ℝ,
      0 ≤ x → 1 ≤ y → 0 < P →
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
            ((-(smoothWeight q Q : ℂ) * A3 n q) *
              (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * A3 n r)).re) ≤
        C * y ^ (3 / 4 : ℝ) := by
  classical
  refine ⟨8 * (45 : ℝ) ^ 131072, by positivity, ?_⟩
  intro x y P Q hx hy hP
  set Qs : Finset ℕ := Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊ with hQs
  let Mq : ℕ → ℝ := fun q => ∏ p ∈ q.primeFactors, (if p = 2 then (45 : ℝ) else 3 + 24 / (p : ℝ))
  have hy0 : (0 : ℝ) < y := by linarith
  have hqpos : ∀ q ∈ Qs, 0 < q := by
    intro q hq
    have h1 : ⌊P⌋₊ < q := (Finset.mem_Ioc.mp hq).1
    omega
  have hqY : ∀ q ∈ Qs, (q : ℝ) ≤ y ^ (1 / 3 : ℝ) := by
    intro q hq
    have h1 : q ≤ ⌊y ^ (1 / 3 : ℝ)⌋₊ := (Finset.mem_Ioc.mp hq).2
    have h2 : (⌊y ^ (1 / 3 : ℝ)⌋₊ : ℝ) ≤ y ^ (1 / 3 : ℝ) := Nat.floor_le (by positivity)
    have h3 : (q : ℝ) ≤ (⌊y ^ (1 / 3 : ℝ)⌋₊ : ℝ) := by exact_mod_cast h1
    linarith
  have hMqnonneg : ∀ q : ℕ, 0 ≤ Mq q := by
    intro q
    apply Finset.prod_nonneg
    intro p hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      exact_mod_cast (Nat.Prime.pos (Nat.prime_of_mem_primeFactors hp))
    split_ifs <;> positivity
  have hcard : ((Qs.card : ℝ)) ≤ 2 * y ^ (1 / 3 : ℝ) := by
    have hsub : Qs ⊆ Finset.range (⌊y ^ (1 / 3 : ℝ)⌋₊ + 1) := by
      intro q hq
      have h1 : q ≤ ⌊y ^ (1 / 3 : ℝ)⌋₊ := (Finset.mem_Ioc.mp hq).2
      exact Finset.mem_range.mpr (by omega)
    have hc : Qs.card ≤ ⌊y ^ (1 / 3 : ℝ)⌋₊ + 1 := by
      simpa using Finset.card_le_card hsub
    have hc' : ((Qs.card : ℝ)) ≤ ((⌊y ^ (1 / 3 : ℝ)⌋₊ : ℝ) + 1) := by
      have hcast : ((Qs.card : ℕ) : ℝ) ≤ ((⌊y ^ (1 / 3 : ℝ)⌋₊ + 1 : ℕ) : ℝ) := by
        exact_mod_cast hc
      simpa using hcast
    have hfloor : (⌊y ^ (1 / 3 : ℝ)⌋₊ : ℝ) ≤ y ^ (1 / 3 : ℝ) := Nat.floor_le (by positivity)
    have hone : (1 : ℝ) ≤ y ^ (1 / 3 : ℝ) := Real.one_le_rpow hy (by norm_num)
    linarith
  have hpair : ∀ q ∈ Qs, ∀ r ∈ Qs.erase q,
      (∑ n ∈ intervalNumbers x y,
        ((-(smoothWeight q Q : ℂ) * A3 n q) *
          (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * A3 n r)).re) ≤ 2 * Mq q * Mq r := by
    intro q hqQ r hrQ
    have hq0 : 0 < q := hqpos q hqQ
    have hr0 : 0 < r := hqpos r (Finset.erase_subset _ _ hrQ)
    have hqr : q ≠ r := (Finset.mem_erase.mp hrQ).1.symm
    have hterm : ∀ n : ℕ,
        ((-(smoothWeight q Q : ℂ) * A3 n q) *
          (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * A3 n r))
        = ((smoothWeight q Q : ℂ) * (smoothWeight r Q : ℂ)) *
            (A3 n q * (starRingEnd ℂ) (A3 n r)) := by
      intro n
      simp only [map_mul, map_neg, Complex.conj_ofReal]
      ring
    have hint : intervalNumbers x y = Finset.Ico (⌊x⌋₊ + 1) (⌊x + y⌋₊ + 1) := by
      rw [intervalNumbers]
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    have hb := Task403b.A3_conjugate_interval_bound (q := q) (r := r) hq0 hr0 hqr
      (⌊x⌋₊ + 1) (⌊x + y⌋₊ + 1)
    have hbq : ∀ n : ℕ, ‖A3 n q‖ ≤ Mq q / (q : ℝ) := by
      intro n
      exact A3_coefficient_bound n q hq0
    have hbr : ∀ n : ℕ, ‖A3 n r‖ ≤ Mq r / (r : ℝ) := by
      intro n
      exact A3_coefficient_bound n r hr0
    have hrange : (∑ n ∈ Finset.range (q * r), ‖A3 n q * (starRingEnd ℂ) (A3 n r)‖)
        ≤ Mq q * Mq r := by
      have hstep : (∑ n ∈ Finset.range (q * r), ‖A3 n q * (starRingEnd ℂ) (A3 n r)‖)
          ≤ ∑ _n ∈ Finset.range (q * r), (Mq q / (q : ℝ)) * (Mq r / (r : ℝ)) := by
        apply Finset.sum_le_sum
        intro n _
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul (hbq n) (hbr n) (norm_nonneg _) (by positivity)
      have hA : (q : ℝ) * (Mq q / (q : ℝ)) = Mq q := by
        have hq0' : (q : ℝ) ≠ 0 := by positivity
        field_simp
      have hBq : (r : ℝ) * (Mq r / (r : ℝ)) = Mq r := by
        have hr0' : (r : ℝ) ≠ 0 := by positivity
        field_simp
      have hval : (∑ _n ∈ Finset.range (q * r), (Mq q / (q : ℝ)) * (Mq r / (r : ℝ)))
          = Mq q * Mq r := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        calc ((q * r : ℕ) : ℝ) * ((Mq q / (q : ℝ)) * (Mq r / (r : ℝ)))
            = ((q : ℝ) * (Mq q / (q : ℝ))) * ((r : ℝ) * (Mq r / (r : ℝ))) := by
              push_cast; ring
          _ = Mq q * Mq r := by rw [hA, hBq]
      rw [hval] at hstep
      exact hstep
    have hwq : ‖(smoothWeight q Q : ℂ)‖ ≤ 1 := Task271b.smoothWeight_norm_le_one q Q
    have hwr : ‖(smoothWeight r Q : ℂ)‖ ≤ 1 := Task271b.smoothWeight_norm_le_one r Q
    have hnrm : ‖((smoothWeight q Q : ℂ) * (smoothWeight r Q : ℂ))‖ ≤ 1 := by
      rw [norm_mul]
      calc ‖(smoothWeight q Q : ℂ)‖ * ‖(smoothWeight r Q : ℂ)‖ ≤ 1 * 1 :=
            mul_le_mul hwq hwr (norm_nonneg _) (by norm_num)
        _ = 1 := by ring
    have hstep1 : (∑ n ∈ intervalNumbers x y,
          ((-(smoothWeight q Q : ℂ) * A3 n q) *
            (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * A3 n r)).re)
        = (∑ n ∈ intervalNumbers x y,
            ((smoothWeight q Q : ℂ) * (smoothWeight r Q : ℂ)) *
              (A3 n q * (starRingEnd ℂ) (A3 n r))).re := by
      simp_rw [hterm, Complex.re_sum]
    have hstep2 : (∑ n ∈ intervalNumbers x y,
            ((smoothWeight q Q : ℂ) * (smoothWeight r Q : ℂ)) *
              (A3 n q * (starRingEnd ℂ) (A3 n r)))
        = ((smoothWeight q Q : ℂ) * (smoothWeight r Q : ℂ)) *
            ∑ n ∈ intervalNumbers x y, (A3 n q * (starRingEnd ℂ) (A3 n r)) := by
      rw [Finset.mul_sum]
    have hstep3 : (((smoothWeight q Q : ℂ) * (smoothWeight r Q : ℂ)) *
          ∑ n ∈ intervalNumbers x y, (A3 n q * (starRingEnd ℂ) (A3 n r))).re
        ≤ ‖((smoothWeight q Q : ℂ) * (smoothWeight r Q : ℂ)) *
          ∑ n ∈ intervalNumbers x y, (A3 n q * (starRingEnd ℂ) (A3 n r))‖ :=
      Complex.re_le_norm _
    have hstep4 : ‖((smoothWeight q Q : ℂ) * (smoothWeight r Q : ℂ)) *
          ∑ n ∈ intervalNumbers x y, (A3 n q * (starRingEnd ℂ) (A3 n r))‖
        ≤ 1 * (2 * ∑ n ∈ Finset.range (q * r), ‖A3 n q * (starRingEnd ℂ) (A3 n r)‖) := by
      rw [norm_mul]
      apply mul_le_mul hnrm _ (norm_nonneg _) (by norm_num)
      rw [hint]
      exact hb
    calc (∑ n ∈ intervalNumbers x y,
          ((-(smoothWeight q Q : ℂ) * A3 n q) *
            (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * A3 n r)).re)
        = (∑ n ∈ intervalNumbers x y,
            ((smoothWeight q Q : ℂ) * (smoothWeight r Q : ℂ)) *
              (A3 n q * (starRingEnd ℂ) (A3 n r))).re := hstep1
      _ = (((smoothWeight q Q : ℂ) * (smoothWeight r Q : ℂ)) *
            ∑ n ∈ intervalNumbers x y, (A3 n q * (starRingEnd ℂ) (A3 n r))).re := by
          rw [hstep2]
      _ ≤ ‖((smoothWeight q Q : ℂ) * (smoothWeight r Q : ℂ)) *
            ∑ n ∈ intervalNumbers x y, (A3 n q * (starRingEnd ℂ) (A3 n r))‖ := hstep3
      _ ≤ 1 * (2 * ∑ n ∈ Finset.range (q * r), ‖A3 n q * (starRingEnd ℂ) (A3 n r)‖) := hstep4
      _ ≤ 1 * (2 * (Mq q * Mq r)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          linarith [hrange]
      _ = 2 * Mq q * Mq r := by ring
  have hsum2 : (∑ q ∈ Qs, ∑ r ∈ Qs.erase q, 2 * Mq q * Mq r) ≤ 2 * (∑ q ∈ Qs, Mq q) ^ 2 := by
    have hstep : (∑ q ∈ Qs, ∑ r ∈ Qs.erase q, 2 * Mq q * Mq r)
        = 2 * ∑ q ∈ Qs, ∑ r ∈ Qs.erase q, Mq q * Mq r := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    rw [hstep]
    have hle : (∑ q ∈ Qs, ∑ r ∈ Qs.erase q, Mq q * Mq r) ≤ (∑ q ∈ Qs, Mq q) ^ 2 := by
      rw [pow_two, Finset.sum_mul_sum]
      apply Finset.sum_le_sum
      intro q _
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      intro r _ _
      exact mul_nonneg (hMqnonneg q) (hMqnonneg r)
    linarith [hle]
  have hMqbound : ∀ q ∈ Qs, Mq q ≤ (45 : ℝ) ^ 65536 * y ^ (1 / 24 : ℝ) := by
    intro q hq
    have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos q hq
    have h1 : Mq q ≤ (45 : ℝ) ^ 65536 * (q : ℝ) ^ (1 / 8 : ℝ) :=
      majorant_power_bound q (hqpos q hq)
    have h2 : (q : ℝ) ^ (1 / 8 : ℝ) ≤ y ^ (1 / 24 : ℝ) := by
      calc (q : ℝ) ^ (1 / 8 : ℝ) ≤ (y ^ (1 / 3 : ℝ)) ^ (1 / 8 : ℝ) :=
            Real.rpow_le_rpow hq0.le (hqY q hq) (by norm_num)
        _ = y ^ (1 / 24 : ℝ) := by
            rw [← Real.rpow_mul hy0.le]
            norm_num
    calc Mq q ≤ (45 : ℝ) ^ 65536 * (q : ℝ) ^ (1 / 8 : ℝ) := h1
      _ ≤ (45 : ℝ) ^ 65536 * y ^ (1 / 24 : ℝ) := by
          apply mul_le_mul_of_nonneg_left h2 (by positivity)
  have hsumq : (∑ q ∈ Qs, Mq q) ≤ (45 : ℝ) ^ 65536 * (2 * y ^ (3 / 8 : ℝ)) := by
    have h1 : (∑ q ∈ Qs, Mq q) ≤ ∑ _q ∈ Qs, ((45 : ℝ) ^ 65536 * y ^ (1 / 24 : ℝ)) :=
      Finset.sum_le_sum hMqbound
    have h2 : (∑ _q ∈ Qs, ((45 : ℝ) ^ 65536 * y ^ (1 / 24 : ℝ)))
        = (Qs.card : ℝ) * ((45 : ℝ) ^ 65536 * y ^ (1 / 24 : ℝ)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    have h3 : (Qs.card : ℝ) * ((45 : ℝ) ^ 65536 * y ^ (1 / 24 : ℝ))
        ≤ (2 * y ^ (1 / 3 : ℝ)) * ((45 : ℝ) ^ 65536 * y ^ (1 / 24 : ℝ)) := by
      apply mul_le_mul_of_nonneg_right hcard
      positivity
    have h4 : (2 * y ^ (1 / 3 : ℝ)) * ((45 : ℝ) ^ 65536 * y ^ (1 / 24 : ℝ))
        = (45 : ℝ) ^ 65536 * (2 * y ^ (3 / 8 : ℝ)) := by
      have hyy : y ^ (1 / 3 : ℝ) * y ^ (1 / 24 : ℝ) = y ^ (3 / 8 : ℝ) := by
        rw [← Real.rpow_add hy0]
        norm_num
      calc (2 * y ^ (1 / 3 : ℝ)) * ((45 : ℝ) ^ 65536 * y ^ (1 / 24 : ℝ))
          = (45 : ℝ) ^ 65536 * (2 * (y ^ (1 / 3 : ℝ) * y ^ (1 / 24 : ℝ))) := by ring
        _ = (45 : ℝ) ^ 65536 * (2 * y ^ (3 / 8 : ℝ)) := by rw [hyy]
    linarith [h1, h2 ▸ h3, h4 ▸ h3]
  have hsq : 2 * ((45 : ℝ) ^ 65536 * (2 * y ^ (3 / 8 : ℝ))) ^ 2
      = 8 * (45 : ℝ) ^ 131072 * y ^ (3 / 4 : ℝ) := by
    have hyy : (y ^ (3 / 8 : ℝ)) ^ 2 = y ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
      norm_num
    have hpw : ((45 : ℝ) ^ 65536) ^ 2 = (45 : ℝ) ^ 131072 := by
      rw [← pow_mul]
    rw [mul_pow, mul_pow, hpw, hyy]
    norm_num
    ring
  calc (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
            ((-(smoothWeight q Q : ℂ) * A3 n q) *
              (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * A3 n r)).re)
      = ∑ q ∈ Qs, ∑ r ∈ Qs.erase q,
          ∑ n ∈ intervalNumbers x y,
            ((-(smoothWeight q Q : ℂ) * A3 n q) *
              (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * A3 n r)).re := by
        rw [hQs]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro q _
        rw [Finset.sum_comm]
    _ ≤ ∑ q ∈ Qs, ∑ r ∈ Qs.erase q, 2 * Mq q * Mq r :=
        Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun r hr => hpair q hq r hr
    _ ≤ 2 * (∑ q ∈ Qs, Mq q) ^ 2 := hsum2
    _ ≤ 2 * ((45 : ℝ) ^ 65536 * (2 * y ^ (3 / 8 : ℝ))) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        have h0 : (0 : ℝ) ≤ ∑ q ∈ Qs, Mq q :=
          Finset.sum_nonneg fun q _ => hMqnonneg q
        exact pow_le_pow_left₀ h0 hsumq 2
    _ = 8 * (45 : ℝ) ^ 131072 * y ^ (3 / 4 : ℝ) := hsq


/-- Page 15 third display. The power saving absorbs every fixed log loss.
CONDITIONAL on off_diagonal_power_bound. -/
theorem off_diagonal_bound (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
            ( (-(smoothWeight q Q : ℂ) * A3 n q) *
              (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * A3 n r)).re) ≤
        C * (y / Real.log x ^ A) := by
  obtain ⟨C, hC, hb⟩ := off_diagonal_power_bound
  obtain ⟨x0, hx0, ha⟩ := Task271b.quarter_power_absorption A ε hε
  refine ⟨C, x0, hC, hx0, ?_⟩
  intro x y P Q hx hy _hyx hP _hPQ _hQ
  have hx2 : 2 ≤ x := hx0.trans hx
  have hy1 : 1 ≤ y := (Real.one_le_rpow (by linarith : 1 ≤ x) hε.le).trans hy
  exact (hb x y P Q (by linarith) hy1 hP).trans
    (mul_le_mul_of_nonneg_left (ha x y hx hy) hC.le)

/-- Page 14 display 51 for j equal to three, assembled by splitting the norm square.
CONDITIONAL on diagonal_bound and off_diagonal_power_bound. -/
theorem tail_mean_square_input (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y, ‖tail3 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) ≤
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
  have heq : (∑ n ∈ intervalNumbers x y, ‖tail3 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) =
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ‖-(smoothWeight q Q : ℂ) * A3 n q‖ ^ 2) +
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
            ((-(smoothWeight q Q : ℂ) * A3 n q) *
              (starRingEnd ℂ) (-(smoothWeight r Q : ℂ) * A3 n r)).re) := by
    simp only [tail3, Task271b.norm_sum_sq_split, Finset.sum_add_distrib]
  rw [heq]
  have hm : 0 ≤ y / P * Real.log x := by positivity
  have he : 0 ≤ y / Real.log x ^ A := by positivity
  calc
    _ ≤ Cd * (y / P * Real.log x) + Co * (y / Real.log x ^ A) := add_le_add hd' ho'
    _ ≤ (Cd + Co) * (y / P * Real.log x + y / Real.log x ^ A) := by nlinarith

/-- Page 14 display 49, Lemma 3.8 for j equal to three.
The statement uses complex norms for the real coefficients.
CONDITIONAL on the three OPEN analytic leaves in this file. -/
theorem lemma38_three :
  ∀ A ε : ℝ, 2 ≤ A → 0 < ε → ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧
    ∀ x y P Q : ℝ, x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y, ‖series3 n P - product3 n Q‖ ^ 2) ≤
        C * (y / P * Real.log x + y / Real.log x ^ A) := by
  intro A ε hA hε
  obtain ⟨Ce, Xe, hCe, hXe, he⟩ := truncation_input A ε hA hε
  obtain ⟨Ct, Xt, hCt, hXt, ht⟩ := tail_mean_square_input A ε hA hε
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
    (fun n => tail3 n P (y ^ (1 / 3 : ℝ)) Q)
    (fun n => (series3 n P - product3 n Q) - tail3 n P (y ^ (1 / 3 : ℝ)) Q)
  simp only [add_sub_cancel] at hs
  have hmain : 0 ≤ y / P * Real.log x := by positivity
  have herr : Ce * (y / Real.log x ^ A) ≤
      Ce * (y / P * Real.log x + y / Real.log x ^ A) := by
    nlinarith
  calc _ ≤ 2 * (∑ n ∈ intervalNumbers x y, ‖tail3 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) +
      2 * (∑ n ∈ intervalNumbers x y,
        ‖(series3 n P - product3 n Q) - tail3 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) := hs
    _ ≤ 2 * (Ct * (y / P * Real.log x + y / Real.log x ^ A)) +
      2 * (Ce * (y / Real.log x ^ A)) := by linarith
    _ ≤ 2 * (Ce + Ct) * (y / P * Real.log x + y / Real.log x ^ A) := by nlinarith

end LeanLab.KumchevLiu2007.Task403c

