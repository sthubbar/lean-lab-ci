/-
The three-square case of Lemma 3.8 on pages 14 and 15.
Three analytic supply leaves remain OPEN. All assemblies are CONDITIONAL on them.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp403b

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


/-- LEAF. Page 14 display 50 and the smooth tail bound immediately below it,
for j equal to three. Only the error after removing the finite tail remains.
The coefficient bound in display 47 and Lemma 3.5 are the analytic inputs. -/
theorem truncation_input (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y,
        ‖(series3 n P - product3 n Q) - tail3 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) ≤
          C * (y / Real.log x ^ A) := by
  sorry

/-- LEAF. Page 15 first display for j equal to three. This is only the
sum over equal moduli, using display 47 and the reciprocal square tail. -/
theorem diagonal_bound :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → 1 ≤ y → y ≤ x → 0 < P →
      (∑ n ∈ intervalNumbers x y,
        ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
          ‖-(smoothWeight q Q : ℂ) * A3 n q‖ ^ 2) ≤
        C * (y / P * Real.log x) := by
  sorry

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
