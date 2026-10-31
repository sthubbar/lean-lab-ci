/-
AI-written Lean code, OpenAI Codex, task33, 2026-10-23, T1.
P0002 Chen 1973, pp. 161 to 162, Lemma 4.
CRT multiplication lifts each character to the product modulus and multiplies them.
The conductor identity gives primitivity in both directions.
Goldbach is open.
-/
import LeanLab.AlmostPrimeSums.Chen1973Lemma4
import LeanLab.AlmostPrimeSums.Chen1973Lemmas

open Finset DirichletCharacter

noncomputable section
namespace LeanLab.AlmostPrimeSums.Chen1973CRT

lemma conductor_mul_of_coprime {n : ℕ} [NeZero n] (χ ψ : DirichletCharacter ℂ n)
    (h : χ.conductor.Coprime ψ.conductor) :
    (χ * ψ).conductor = χ.conductor * ψ.conductor := by
  apply Nat.dvd_antisymm
  · simpa only [h.lcm_eq_mul] using conductor_mul_dvd_lcm_conductor χ ψ
  · have hχ : χ.conductor ∣ (χ * ψ).conductor * ψ.conductor := by
      have he : χ = (χ * ψ) * ψ⁻¹ := by simp
      have hd := conductor_mul_dvd_lcm_conductor (χ * ψ) ψ⁻¹
      rw [← he, conductor_inv] at hd
      exact hd.trans (Nat.lcm_dvd_mul _ _)
    have hψ : ψ.conductor ∣ χ.conductor * (χ * ψ).conductor := by
      have he : ψ = χ⁻¹ * (χ * ψ) := by simp
      have hd := conductor_mul_dvd_lcm_conductor χ⁻¹ (χ * ψ)
      rw [← he, conductor_inv] at hd
      exact hd.trans (Nat.lcm_dvd_mul _ _)
    exact h.mul_dvd_of_dvd_of_dvd ((h.dvd_mul_right).mp hχ) ((h.symm.dvd_mul_left).mp hψ)

/-- CRT multiplication by lifting both characters to the product modulus. -/
def crtMul {a b : ℕ} (χ : DirichletCharacter ℂ a) (ψ : DirichletCharacter ℂ b) :
    DirichletCharacter ℂ (a * b) :=
  changeLevel (dvd_mul_right a b) χ * changeLevel (dvd_mul_left b a) ψ

lemma conductor_crtMul {a b : ℕ} [NeZero (a * b)] (h : a.Coprime b)
    (χ : DirichletCharacter ℂ a) (ψ : DirichletCharacter ℂ b) :
    (crtMul χ ψ).conductor = χ.conductor * ψ.conductor := by
  unfold crtMul
  rw [conductor_mul_of_coprime]
  · rw [conductor_changeLevel, conductor_changeLevel]
  · rw [conductor_changeLevel, conductor_changeLevel]
    exact h.of_dvd (conductor_dvd_level χ) (conductor_dvd_level ψ)

def crtMap (a b : ℕ) : (DirichletCharacter ℂ a × DirichletCharacter ℂ b) →*
    DirichletCharacter ℂ (a * b) where
  toFun x := crtMul x.1 x.2
  map_one' := by simp [crtMul]
  map_mul' x y := by simp [crtMul, map_mul, mul_mul_mul_comm]

lemma crtMap_injective {a b : ℕ} [NeZero (a * b)] (h : a.Coprime b) :
    Function.Injective (crtMap a b) := by
  have : NeZero a := ⟨left_ne_zero_of_mul (NeZero.ne (a * b))⟩
  have : NeZero b := ⟨right_ne_zero_of_mul (NeZero.ne (a * b))⟩
  apply (injective_iff_map_eq_one (crtMap a b)).mpr
  intro x hx
  change crtMul x.1 x.2 = 1 at hx
  have hc : x.1.conductor * x.2.conductor = 1 := by
    rw [← conductor_crtMul h, hx, conductor_one]
  have h1 : x.1.conductor = 1 := Nat.dvd_one.mp (by
    rw [← hc]
    exact dvd_mul_right _ _)
  have h2 : x.2.conductor = 1 := Nat.dvd_one.mp (by
    rw [← hc]
    exact dvd_mul_left _ _)
  exact Prod.ext ((eq_one_iff_conductor_eq_one (χ := x.1)).mpr h1)
    ((eq_one_iff_conductor_eq_one (χ := x.2)).mpr h2)

lemma crtMap_bijective {a b : ℕ} [NeZero (a * b)] (h : a.Coprime b) :
    Function.Bijective (crtMap a b) := by
  classical
  have : NeZero a := ⟨left_ne_zero_of_mul (NeZero.ne (a * b))⟩
  have : NeZero b := ⟨right_ne_zero_of_mul (NeZero.ne (a * b))⟩
  apply (Fintype.bijective_iff_injective_and_card (crtMap a b)).mpr
  refine ⟨crtMap_injective h, ?_⟩
  rw [Fintype.card_prod]
  simp only [← Nat.card_eq_fintype_card,
    card_eq_totient_of_hasEnoughRootsOfUnity, Nat.totient_mul h]

lemma isPrimitive_crtMul_iff {a b : ℕ} [NeZero (a * b)] (h : a.Coprime b)
    (χ : DirichletCharacter ℂ a) (ψ : DirichletCharacter ℂ b) :
    (crtMul χ ψ).IsPrimitive ↔ χ.IsPrimitive ∧ ψ.IsPrimitive := by
  have ha0 : 0 < a := Nat.pos_of_ne_zero (left_ne_zero_of_mul (NeZero.ne (a * b)))
  have hb0 : 0 < b := Nat.pos_of_ne_zero (right_ne_zero_of_mul (NeZero.ne (a * b)))
  rw [isPrimitive_def, conductor_crtMul h, isPrimitive_def, isPrimitive_def]
  constructor
  · intro he
    have hca : χ.conductor ≤ a := Nat.le_of_dvd ha0 (conductor_dvd_level χ)
    have hcb : ψ.conductor ≤ b := Nat.le_of_dvd hb0 (conductor_dvd_level ψ)
    have hea : χ.conductor = a := by
      apply le_antisymm hca
      by_contra hlt
      have hp : χ.conductor < a := Nat.lt_of_not_ge hlt
      have h1 := Nat.mul_le_mul_left χ.conductor hcb
      have h2 := Nat.mul_lt_mul_of_pos_right hp hb0
      omega
    refine ⟨hea, ?_⟩
    rw [hea] at he
    exact Nat.eq_of_mul_eq_mul_left ha0 he
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

lemma crtMul_apply_int {a b : ℕ} (χ : DirichletCharacter ℂ a) (ψ : DirichletCharacter ℂ b)
    (m : ℤ) (hm : IsCoprime m (a * b : ℕ)) :
    crtMul χ ψ (m : ZMod (a * b)) = χ (m : ZMod a) * ψ (m : ZMod b) := by
  rw [crtMul, MulChar.mul_apply, changeLevel_eq_cast_of_dvd' χ _ hm,
    changeLevel_eq_cast_of_dvd' ψ _ hm]

lemma primSum_mul_of_coprime {a b : ℕ} [NeZero (a * b)] (h : a.Coprime b)
    (m : ℤ) (hm : IsCoprime m (a * b : ℕ)) :
    Chen1973Lemma4.primSum (a * b) m = Chen1973Lemma4.primSum a m * Chen1973Lemma4.primSum b m := by
  classical
  have : NeZero a := ⟨left_ne_zero_of_mul (NeZero.ne (a * b))⟩
  have : NeZero b := ⟨right_ne_zero_of_mul (NeZero.ne (a * b))⟩
  unfold Chen1973Lemma4.primSum
  symm
  rw [sum_mul_sum]
  rw [← sum_product (f := fun x : DirichletCharacter ℂ a × DirichletCharacter ℂ b =>
    x.1 (m : ZMod a) * x.2 (m : ZMod b))]
  apply sum_bij (fun x _ => crtMap a b x)
  · intro x hx
    obtain ⟨h1, h2⟩ := mem_product.mp hx
    simp only [mem_filter, mem_univ, true_and] at h1 h2 ⊢
    exact (isPrimitive_crtMul_iff h x.1 x.2).mpr ⟨h1, h2⟩
  · intro x _ y _ he
    exact crtMap_injective h he
  · intro χ hχ
    obtain ⟨x, hx⟩ := (crtMap_bijective h).2 χ
    refine ⟨x, ?_, hx⟩
    rw [mem_product]
    have hp := (mem_filter.mp hχ).2
    rw [← hx] at hp
    have hs := (isPrimitive_crtMul_iff h x.1 x.2).mp hp
    exact ⟨mem_filter.mpr ⟨mem_univ _, hs.1⟩, mem_filter.mpr ⟨mem_univ _, hs.2⟩⟩
  · intro x _
    exact (crtMul_apply_int x.1 x.2 m hm).symm

lemma primSum_eq_zero_of_not_coprime {k : ℕ} (m : ℤ) (hm : ¬ IsCoprime m (k : ℤ)) :
    Chen1973Lemma4.primSum k m = 0 := by
  classical
  unfold Chen1973Lemma4.primSum
  exact sum_eq_zero (fun χ _ => (DirichletCharacter.apply_eq_zero_iff χ m).mpr hm)

lemma primSum_mul {a b : ℕ} [NeZero (a * b)] (h : a.Coprime b) (m : ℤ) :
    Chen1973Lemma4.primSum (a * b) m = Chen1973Lemma4.primSum a m * Chen1973Lemma4.primSum b m := by
  by_cases hm : IsCoprime m (a * b : ℕ)
  · exact primSum_mul_of_coprime h m hm
  · rw [primSum_eq_zero_of_not_coprime m hm]
    by_cases hma : IsCoprime m (a : ℤ)
    · by_cases hmb : IsCoprime m (b : ℤ)
      · exfalso
        apply hm
        simpa only [Nat.cast_mul] using hma.mul_right hmb
      · rw [primSum_eq_zero_of_not_coprime m hmb, mul_zero]
    · rw [primSum_eq_zero_of_not_coprime m hma, zero_mul]

lemma primSum_one (m : ℤ) : Chen1973Lemma4.primSum 1 m = 1 := by
  have hp : ∀ χ : DirichletCharacter ℂ 1, χ.IsPrimitive := by
    intro χ
    exact Nat.dvd_one.mp (conductor_dvd_level χ)
  have he : Chen1973Lemma4.primSum 1 m = ∑ χ : DirichletCharacter ℂ 1, χ (m : ZMod 1) := by
    simp [Chen1973Lemma4.primSum, hp]
  rw [he, Chen1973Lemma4.sum_all_eq_gFull (by decide), Chen1973Lemma4.gFull]
  simp

/-- Chen Lemma 4 from the prime case by the CRT multiplicativity just proved. -/
theorem chen_lemma4_via_CRT {k : ℕ} (hk : Squarefree k) (m : ℤ) :
    ‖Chen1973Lemma4.primSum k m‖ ≤ (Int.gcd (m - 1) k : ℝ) := by
  revert hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    by_cases hk1 : k = 1
    · subst hk1
      rw [primSum_one, norm_one]
      simp
    obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd hk1
    obtain ⟨n, rfl⟩ := hpk
    obtain ⟨hcop, hpsq, hnsq⟩ := Nat.squarefree_mul_iff.mp hk
    have hn : 0 < n := Nat.pos_of_ne_zero hnsq.ne_zero
    have hnlt : n < p * n := by nlinarith [hp.one_lt]
    have : NeZero (p * n) := ⟨hk.ne_zero⟩
    have : Fact p.Prime := ⟨hp⟩
    have hprime := Chen1973Lemmas.chen_lemma4_prime (p := p) m
    change ‖Chen1973Lemma4.primSum p m‖ ≤ (Int.gcd (m - 1) p : ℝ) at hprime
    have hind := ih n hnlt hnsq
    have hg : Int.gcd (m - 1) (p * n : ℕ) = Int.gcd (m - 1) p * Int.gcd (m - 1) n := by
      simp only [Int.gcd, Int.natAbs_natCast]
      exact Nat.Coprime.gcd_mul _ hcop
    rw [primSum_mul hcop, norm_mul, hg, Nat.cast_mul]
    exact mul_le_mul hprime hind (norm_nonneg _) (Nat.cast_nonneg _)

theorem chen_lemma4_as_stated_via_CRT {k : ℕ} (hk : Squarefree k) (_hodd : Odd k)
    {m : ℤ} (_hm : m ≠ 1) :
    ‖Chen1973Lemma4.primSum k m‖ ≤ (Int.gcd (m - 1) k : ℝ) :=
  chen_lemma4_via_CRT hk m

example : ‖Chen1973Lemma4.primSum 15 7‖ ≤ 3 := by
  have h := chen_lemma4_via_CRT (k := 15) (Nat.squarefree_mul_iff.mpr
    ⟨by decide, Nat.prime_three.squarefree, Nat.prime_five.squarefree⟩ : Squarefree (3 * 5)) 7
  exact h

end LeanLab.AlmostPrimeSums.Chen1973CRT

#print axioms LeanLab.AlmostPrimeSums.Chen1973CRT.conductor_mul_of_coprime

#print axioms LeanLab.AlmostPrimeSums.Chen1973CRT.conductor_crtMul

#print axioms LeanLab.AlmostPrimeSums.Chen1973CRT.crtMap_injective

#print axioms LeanLab.AlmostPrimeSums.Chen1973CRT.crtMap_bijective

#print axioms LeanLab.AlmostPrimeSums.Chen1973CRT.isPrimitive_crtMul_iff

#print axioms LeanLab.AlmostPrimeSums.Chen1973CRT.crtMul_apply_int

#print axioms LeanLab.AlmostPrimeSums.Chen1973CRT.primSum_mul_of_coprime

#print axioms LeanLab.AlmostPrimeSums.Chen1973CRT.primSum_eq_zero_of_not_coprime

#print axioms LeanLab.AlmostPrimeSums.Chen1973CRT.primSum_mul

#print axioms LeanLab.AlmostPrimeSums.Chen1973CRT.primSum_one

#print axioms LeanLab.AlmostPrimeSums.Chen1973CRT.chen_lemma4_via_CRT

#print axioms LeanLab.AlmostPrimeSums.Chen1973CRT.chen_lemma4_as_stated_via_CRT
