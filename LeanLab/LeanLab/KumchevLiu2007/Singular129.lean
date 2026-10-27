/-
The three-square singular factor of Kumchev and Liu, arXiv 0801.0130,
page 13 display 45 and property iv. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp129b
open Real Complex LeanLab.KumchevLiu2007 LeanLab.KumchevLiu2007.U1534
attribute [local instance] Classical.propDecidable
namespace LeanLab.KumchevLiu2007.Task129c
/-- Page 13 display 45. The three-square singular coefficient. -/
noncomputable def A3 (n q : ℕ) : ℂ :=
  1 / ((Nat.totient q : ℂ) ^ 3) *
    ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      gaussS q a ^ 3 * ee (-((a * n : ℕ) : ℝ) / q)
/-- Page 13 property iv. The nonzero local triples representing n. -/
noncomputable def tripleRoots (p : ℕ) [NeZero p] (n : ℕ) : Finset ((ZMod p × ZMod p) × ZMod p) :=
  let s := Finset.univ.erase (0 : ZMod p)
  ((s.product s).product s).filter (fun v => v.1.1 ^ 2 + v.1.2 ^ 2 + v.2 ^ 2 = (n : ZMod p))
/-- Page 13 display 45 and property iv. Character orthogonality expresses
the prime factor through its local representation count. -/
theorem A3_prime_count (p : ℕ) [Fact p.Prime] (n : ℕ) :
    A3 n p = (p : ℂ) * ((tripleRoots p n).card : ℂ) / ((p : ℂ) - 1)^3 - 1 := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  have std_int (a : ℤ) : ee ((a : ℝ) / p) = ZMod.stdAddChar (a : ZMod p) := by
    rw [ZMod.stdAddChar_coe]
    unfold ee
    congr 1
    push_cast
    ring
  have std_nat (a : ℕ) : ee ((a : ℝ) / p) = ZMod.stdAddChar (a : ZMod p) := by
    simpa using std_int (a : ℤ)
  have sum_range (f : ZMod p → ℂ) :
      ∑ a ∈ Finset.range p, f (a : ZMod p) = ∑ a : ZMod p, f a := by
    apply Finset.sum_bij (s := Finset.range p) (t := (Finset.univ : Finset (ZMod p))) (fun a _ => (a : ZMod p))
    · intro a ha; exact Finset.mem_univ _
    · intro a ha b hb hab
      have h := congrArg ZMod.val hab
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha),
        Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] using h
    · intro a ha
      exact ⟨a.val, Finset.mem_range.mpr (ZMod.val_lt a), ZMod.natCast_zmod_val a⟩
    · intro a ha; rfl
  have coprime_iff (a : ℕ) : Nat.Coprime a p ↔ (a : ZMod p) ≠ 0 := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd, ne_eq, ZMod.natCast_eq_zero_iff]
  have filtered (f : ZMod p → ℂ) :
      ∑ a ∈ (Finset.range p).filter (fun a => Nat.Coprime a p), f (a : ZMod p) =
      ∑ a ∈ (Finset.univ.erase (0 : ZMod p)), f a := by
    rw [Finset.sum_filter]
    simp_rw [coprime_iff]
    rw [sum_range (fun a => if a ≠ 0 then f a else 0)]
    rw [← Finset.sum_filter]
    congr 1
    ext a
    simp
  have std_neg (a : ℕ) : ee (-((a * n : ℕ) : ℝ) / p) =
      ZMod.stdAddChar (-((a : ZMod p) * (n : ZMod p))) := by
    have heq : -((a * n : ℕ) : ℝ) / p = ((-((a * n : ℕ) : ℤ) : ℤ) : ℝ) / p := by
      push_cast; ring
    rw [heq, std_int]
    push_cast
    rfl
  let s := Finset.univ.erase (0 : ZMod p)
  let T := (s.product s).product s
  have gauss_eq (a : ℕ) : gaussS p a =
      ∑ x ∈ s, ZMod.stdAddChar ((a : ZMod p) * x ^ 2) := by
    unfold gaussS
    simp_rw [std_nat, Nat.cast_mul, Nat.cast_pow]
    exact filtered (fun x => ZMod.stdAddChar ((a : ZMod p) * x ^ 2))
  have cube_eq (a : ℕ) : gaussS p a ^ 3 * ee (-((a*n : ℕ) : ℝ)/p) =
      ∑ v ∈ T, ZMod.stdAddChar ((a : ZMod p) *
        (v.1.1 ^ 2 + v.1.2 ^ 2 + v.2 ^ 2 - (n : ZMod p))) := by
    rw [gauss_eq, std_neg]
    dsimp only [T]
    simp only [Finset.product_eq_sprod, Finset.sum_product]
    simp only [pow_succ, pow_zero, one_mul,
      Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro z hz
    rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  have hchar (t : ZMod p) :
      ∑ a ∈ Finset.univ.erase (0 : ZMod p), ZMod.stdAddChar (a * t) =
        if t = 0 then (p : ℂ) - 1 else -1 := by
    have ht := AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := p)) t
      (ZMod.isPrimitive_stdAddChar p)
    have hs := Finset.sum_erase_add (s := Finset.univ)
      (f := fun a : ZMod p => ZMod.stdAddChar (a * t)) (Finset.mem_univ 0)
    simp only [zero_mul, AddChar.map_zero_eq_one] at hs
    rw [ht, ZMod.card] at hs
    by_cases ht0 : t = 0
    · simp only [ht0, ite_true] at hs ⊢
      linear_combination hs
    · simp only [ht0, ite_false, Nat.cast_zero] at hs ⊢
      linear_combination hs
  have hg : ∑ a ∈ (Finset.range p).filter (fun a => Nat.Coprime a p),
      gaussS p a ^ 3 * ee (-((a*n : ℕ) : ℝ)/p) =
      (p : ℂ) * ((tripleRoots p n).card : ℂ) - ((p : ℂ) - 1)^3 := by
    simp_rw [cube_eq]
    rw [filtered (fun a => ∑ v ∈ T, ZMod.stdAddChar
      (a * (v.1.1 ^ 2 + v.1.2 ^ 2 + v.2 ^ 2 - (n : ZMod p)))), Finset.sum_comm]
    simp_rw [hchar, sub_eq_zero]
    have heq (v : (ZMod p × ZMod p) × ZMod p) :
        (if v.1.1 ^ 2 + v.1.2 ^ 2 + v.2 ^ 2 = (n : ZMod p) then (p : ℂ) - 1 else -1) =
        (p : ℂ) * (if v.1.1 ^ 2 + v.1.2 ^ 2 + v.2 ^ 2 = (n : ZMod p) then 1 else 0) - 1 := by
      split_ifs <;> ring
    simp_rw [heq, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hR : (∑ v ∈ T, if v.1.1 ^ 2 + v.1.2 ^ 2 + v.2 ^ 2 = (n : ZMod p)
        then (1 : ℂ) else 0) = (tripleRoots p n).card := by
      simp [tripleRoots, T, s]
    rw [hR]
    simp [T, s, ZMod.card, Nat.cast_sub hp.one_le]
    ring
  unfold A3
  rw [hg, Nat.totient_prime hp]
  norm_num only [Nat.cast_sub hp.one_le, Nat.cast_one]
  have hpC : (p : ℂ) - 1 ≠ 0 := by
    have hp2 := hp.two_le
    exact_mod_cast (show (p : ℤ) - 1 ≠ 0 by omega)
  field_simp
/-- Page 13 property iv. A local unit square representation gives a
nonempty finite solution set. -/
theorem tripleRoots_nonempty {p n : ℕ} [NeZero p] (hloc : LocSol3 p n) :
    (tripleRoots p n).Nonempty := by
  obtain ⟨x, y, z, hx, hy, hz, heq⟩ := hloc
  refine ⟨((x,y),z), ?_⟩
  simp [tripleRoots, hx, hy, hz, heq]

/-- Page 13 property iv. A nonzero local representation makes the
three-square prime local factor positive. -/
theorem A3_factor_pos_of_local (p : ℕ) [Fact p.Prime] (n : ℕ) (hloc : LocSol3 p n) :
    0 < (1 + A3 n p).re := by
  have hp : p.Prime := Fact.out
  have hcard : 0 < (tripleRoots p n).card :=
    Finset.card_pos.mpr (tripleRoots_nonempty hloc)
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hcR : (0 : ℝ) < (tripleRoots p n).card := by exact_mod_cast hcard
  have heq : 1 + A3 n p =
      ((((p : ℝ) * ((tripleRoots p n).card : ℝ)) / ((p : ℝ) - 1)^3 : ℝ) : ℂ) := by
    rw [A3_prime_count]
    push_cast
    ring
  rw [heq, Complex.ofReal_re]
  positivity

/-- Page 13 property iv. The prime local factors for n in H3 are positive. -/
theorem A3_factor_positive_of_InH3 {n p : ℕ} (hn : InH3 n) (hp : p.Prime) :
    0 < (1 + A3 n p).re := by
  have : Fact p.Prime := ⟨hp⟩
  exact A3_factor_pos_of_local p n (locSol3_of_InH3 hn hp)

/-- Page 3, exponential notation. The analytic exponential agrees with
the standard additive character on an integer residue. -/
lemma ee_int_bridge (q : ℕ) [NeZero q] (a : ℤ) :
    ee ((a : ℝ) / q) = ZMod.stdAddChar (a : ZMod q) := by
  rw [ZMod.stdAddChar_coe]
  unfold ee
  congr 1
  push_cast
  ring

/-- Page 2 display 8. When every unit square is one modulo q, the
Gauss sum is the totient times the additive character at a. -/
lemma gauss_unit_sq (q : ℕ) [NeZero q] (a : ℕ)
    (hunit : ∀ x ∈ (Finset.range q).filter (fun x => x.Coprime q), (x : ZMod q)^2 = 1) :
    gaussS q a = (q.totient : ℂ) * ZMod.stdAddChar (a : ZMod q) := by
  have hnat (b : ℕ) : ee ((b : ℝ) / q) = ZMod.stdAddChar (b : ZMod q) := by
    simpa using ee_int_bridge q (b : ℤ)
  unfold gaussS
  have heq : (∑ x ∈ (Finset.range q).filter (fun x => x.Coprime q),
      ee (((a*x^2 : ℕ) : ℝ)/q)) =
      ∑ x ∈ (Finset.range q).filter (fun x => x.Coprime q), ZMod.stdAddChar (a : ZMod q) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [hnat]
    push_cast
    rw [hunit x hx, mul_one]
  rw [heq]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Nat.totient_eq_card_coprime]
  simp only [Nat.coprime_comm]

/-- Page 13 display 45. If unit squares are one modulo q and n is three
modulo q, the three-square coefficient equals the totient. -/
lemma A3_unit_sq (q : ℕ) [NeZero q] (n : ℕ) (hn : (n : ZMod q) = 3)
    (hunit : ∀ x ∈ (Finset.range q).filter (fun x => x.Coprime q), (x : ZMod q)^2 = 1) :
    A3 n q = (q.totient : ℂ) := by
  have he (a : ℕ) : ee (-((a*n : ℕ) : ℝ)/q) = ZMod.stdAddChar (-((a*n : ℕ) : ZMod q)) := by
    have hcast : -((a*n : ℕ) : ℝ)/q = ((-((a*n : ℕ) : ℤ) : ℤ) : ℝ)/q := by push_cast; ring
    rw [hcast, ee_int_bridge]
    push_cast
    rfl
  have ht (a : ℕ) : gaussS q a ^ 3 * ee (-((a*n : ℕ) : ℝ)/q) = (q.totient : ℂ)^3 := by
    rw [gauss_unit_sq q a hunit, mul_pow, he]
    have hc : ZMod.stdAddChar (a : ZMod q)^3 * ZMod.stdAddChar (-((a*n : ℕ) : ZMod q)) = 1 := by
      simp only [pow_succ, pow_zero, one_mul]
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      have hz : (a : ZMod q) + (a : ZMod q) + (a : ZMod q) + -((a*n : ℕ) : ZMod q) = 0 := by
        push_cast
        rw [hn]
        ring
      rw [hz, AddChar.map_zero_eq_one]
    calc (q.totient : ℂ)^3 * ZMod.stdAddChar (a : ZMod q)^3 *
        ZMod.stdAddChar (-((a*n : ℕ) : ZMod q)) =
        (q.totient : ℂ)^3 * (ZMod.stdAddChar (a : ZMod q)^3 *
          ZMod.stdAddChar (-((a*n : ℕ) : ZMod q))) := by ring
      _ = _ := by rw [hc, mul_one]
  unfold A3
  simp_rw [ht]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.range q).filter (fun x => x.Coprime q)).card = q.totient := by
    rw [Nat.totient_eq_card_coprime]
    simp only [Nat.coprime_comm]
  rw [hcard]
  have hphi : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  field_simp

/-- Page 13 property iv, at the prime two. -/
theorem A3_two_of_InH3 {n : ℕ} (hn : InH3 n) : A3 n 2 = 1 := by
  have hnZ : (n : ZMod 2) = 3 := by
    rw [← ZMod.natCast_mod n 2]
    have hmod : n % 2 = 1 := by have := hn.1; omega
    rw [hmod]; rfl
  rw [A3_unit_sq 2 n hnZ (by decide)]
  exact_mod_cast (show Nat.totient 2 = 1 by decide)

/-- Page 13 property iv, at the second power of two. -/
theorem A3_four_of_InH3 {n : ℕ} (hn : InH3 n) : A3 n 4 = 2 := by
  have hnZ : (n : ZMod 4) = 3 := by
    rw [← ZMod.natCast_mod n 4]
    have hmod : n % 4 = 3 := by have := hn.1; omega
    rw [hmod]; rfl
  rw [A3_unit_sq 4 n hnZ (by decide)]
  exact_mod_cast (show Nat.totient 4 = 2 by decide)

/-- Page 13 property iv, at the third power of two. -/
theorem A3_eight_of_InH3 {n : ℕ} (hn : InH3 n) : A3 n 8 = 4 := by
  have hnZ : (n : ZMod 8) = 3 := by
    rw [← ZMod.natCast_mod n 8]
    have hmod : n % 8 = 3 := by have := hn.1; omega
    rw [hmod]; rfl
  rw [A3_unit_sq 8 n hnZ (by decide)]
  exact_mod_cast (show Nat.totient 8 = 4 by decide)

/-- Page 13 property iv. The finite contribution through the third power
of two is eight. No assertion about higher prime powers is used here. -/
theorem A3_two_partial_factor {n : ℕ} (hn : InH3 n) :
    1 + A3 n 2 + A3 n 4 + A3 n 8 = 8 := by
  rw [A3_two_of_InH3 hn, A3_four_of_InH3 hn, A3_eight_of_InH3 hn]
  norm_num

end LeanLab.KumchevLiu2007.Task129c
