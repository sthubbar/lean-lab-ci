/-
ROUTE BURST 7, DtRS1998 first_family_remaining.
AI wrote this Lean code. Binary Goldbach is OPEN.

P0037 Section 5.1 page 211, the finite primality certification paragraph.
The N + 1 Lucas test and the combined N - 1 and N + 1 test of
Brillhart, Lehmer and Selfridge 1975, Math. Comp. 29, Theorems 13 and 14
in spirit: if N + 1 = F2 R2 and a Lucas pair P, Q with D = P^2 - 4Q prime
to N gives gamma = alpha / beta of order divisible by F2 modulo every prime
factor r of N, then r = 1 or r = -1 modulo F2. Together with the N - 1 part
of `PocklingtonB7.pock_factor`, every prime factor r of N is either 1 modulo
lcm F1 F2, or the single residue s0 = 1 mod F1 and -1 mod F2 below that lcm.

The arithmetic is done in AdjoinRoot of X^2 - P X + Q over ZMod r, with the
kernel computing in pairs u + v alpha modulo N. No native_decide, no axioms.
-/
import Mathlib
import LeanLab.DtRS1998.PocklingtonB7

namespace LeanLab.DtRS1998.PocklingtonB7

open Polynomial

/-- Multiplication of `x.1 + x.2 α` and `y.1 + y.2 α` modulo `n` with
`α ^ 2 = P α - Q`, where `nQ` stands for `- Q` modulo `n`. -/
def qmul (n P nQ : ℕ) (x y : ℕ × ℕ) : ℕ × ℕ :=
  ((x.1 * y.1 + nQ * (x.2 * y.2)) % n, (x.1 * y.2 + x.2 * y.1 + P * (x.2 * y.2)) % n)

/-- Binary power in the pair ring, with fuel. -/
def qpow : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ → ℕ → ℕ × ℕ
  | 0, n, _, _, _, _ => (1 % n, 0)
  | fuel + 1, n, P, nQ, x, e =>
    if e = 0 then (1 % n, 0) else
      let h := qpow fuel n P nQ x (e / 2)
      let h2 := qmul n P nQ h h
      if e % 2 = 1 then qmul n P nQ h2 x else h2

section cast

variable {A : Type*} [CommRing A]

theorem cast_mod_of_zero {n : ℕ} (hn : (n : A) = 0) (a : ℕ) : ((a % n : ℕ) : A) = a := by
  conv_rhs => rw [← Nat.mod_add_div a n]
  simp [hn]

/-- The pair `x` read in `A` at `α`. -/
def qval (α : A) (x : ℕ × ℕ) : A := (x.1 : A) + (x.2 : A) * α

theorem qmul_val {n P Q nQ : ℕ} {α : A} (hn : (n : A) = 0) (hα : α ^ 2 = P * α - Q)
    (hQ : (nQ : A) = -Q) (x y : ℕ × ℕ) :
    qval α (qmul n P nQ x y) = qval α x * qval α y := by
  simp only [qval, qmul, cast_mod_of_zero hn, Nat.cast_add, Nat.cast_mul, hQ]
  linear_combination (-((x.2 : A) * (y.2 : A))) * hα

theorem qpow_val {n P Q nQ : ℕ} {α : A} (hn : (n : A) = 0) (hα : α ^ 2 = P * α - Q)
    (hQ : (nQ : A) = -Q) : ∀ fuel (x : ℕ × ℕ) e, e < 2 ^ fuel →
    qval α (qpow fuel n P nQ x e) = qval α x ^ e := by
  intro fuel
  induction fuel with
  | zero => intro x e he; simp at he; subst he; simp [qpow, qval, cast_mod_of_zero hn]
  | succ k ih =>
    intro x e he
    simp only [qpow]
    by_cases h0 : e = 0
    · subst h0; simp [qval, cast_mod_of_zero hn]
    · rw [if_neg h0]
      have hlt : e / 2 < 2 ^ k := by rw [pow_succ] at he; omega
      have IH := ih x (e / 2) hlt
      have he2 : e = 2 * (e / 2) + e % 2 := (Nat.div_add_mod e 2).symm
      by_cases h1 : e % 2 = 1
      · rw [if_pos h1, qmul_val hn hα hQ, qmul_val hn hα hQ, IH]
        conv_rhs => rw [he2, h1, pow_add, pow_mul, pow_one]
        ring
      · rw [if_neg h1, qmul_val hn hα hQ, IH]
        have h1' : e % 2 = 0 := by omega
        conv_rhs => rw [he2, h1', add_zero, pow_mul]
        ring

end cast

/-- A monoid element whose `m`-th power is one while each `m / p`-th power for the
listed primes is not has order divisible by the listed prime power product. -/
theorem prodPow_dvd_orderOf {M : Type*} [Monoid M] (b : M) (m : ℕ) (L : List (ℕ × ℕ))
    (hc : chain 0 L = true) (hprimes : ∀ x ∈ L, x.1.Prime) (hF : prodPow L ∣ m)
    (hb : b ^ m = 1) (hne : ∀ x ∈ L, b ^ (m / x.1) ≠ 1) : prodPow L ∣ orderOf b := by
  set u := orderOf b
  have hu_m : u ∣ m := orderOf_dvd_of_pow_eq_one hb
  apply prodPow_dvd u L 0 hc hprimes
  intro x hx
  have hxp := hprimes x hx
  have hndiv : ¬ u ∣ m / x.1 := fun h => hne x hx (orderOf_dvd_iff_pow_eq_one.mp h)
  obtain ⟨w, hw⟩ := hu_m
  have hpw : ¬ x.1 ∣ w := by
    rintro ⟨w', rfl⟩
    apply hndiv
    have : m / x.1 = u * w' := by
      rw [hw, show u * (x.1 * w') = x.1 * (u * w') by ring]
      exact Nat.mul_div_cancel_left _ hxp.pos
    rw [this]; exact Dvd.intro _ rfl
  have hxF : x.1 ^ x.2 ∣ m := (pow_dvd_prodPow L x hx).trans hF
  rw [hw] at hxF
  exact Nat.Coprime.dvd_of_dvd_mul_right
    (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hxp).mpr hpw)) hxF

/-- The Frobenius dichotomy for a root of `X^2 - P X + Q` over `ZMod r`, in the
quotient ring: the element `γ = Qi α^2`, which is `α / β`, satisfies
`γ^(r-1) = 1` or `γ^(r+1) = 1`, provided `P^2 - 4Q` is a unit modulo `r`. -/
theorem frob_dichotomy (r : ℕ) [hr : Fact r.Prime] (P Q Qi : ℕ)
    (hQi : ((Q * Qi : ℕ) : ZMod r) = 1)
    (hD : ((P * P : ℕ) : ZMod r) - 4 * (Q : ZMod r) ≠ 0) :
    let f : (ZMod r)[X] := C 1 * X ^ 2 + C (-(P : ZMod r)) * X + C (Q : ZMod r)
    let α := AdjoinRoot.root f
    let γ := ((Qi : ℕ) : AdjoinRoot f) * α ^ 2
    γ ^ (r - 1) = 1 ∨ γ ^ (r + 1) = 1 := by
  intro f α γ
  have hdeg : f.natDegree = 2 := natDegree_quadratic one_ne_zero
  have hdeg' : f.degree ≠ 0 := by
    rw [degree_eq_natDegree (by intro h; rw [h] at hdeg; simp at hdeg), hdeg]; decide
  have hinj : Function.Injective (algebraMap (ZMod r) (AdjoinRoot f)) :=
    AdjoinRoot.of.injective_of_degree_ne_zero hdeg'
  have : CharP (AdjoinRoot f) r := charP_of_injective_algebraMap hinj r
  have hroot : α ^ 2 - (P : AdjoinRoot f) * α + (Q : AdjoinRoot f) = 0 := by
    have h := AdjoinRoot.eval₂_root f
    simp only [f, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, eval₂_pow, eval₂_neg, eval₂_natCast,
      map_one, map_neg, map_natCast, one_mul] at h
    linear_combination h
  set β : AdjoinRoot f := (P : AdjoinRoot f) - α with hβ
  have hαβ : α * β = Q := by rw [hβ]; linear_combination -hroot
  have hQiA : ((Qi : ℕ) : AdjoinRoot f) * (Q : AdjoinRoot f) = 1 := by
    have := congrArg (algebraMap (ZMod r) (AdjoinRoot f)) hQi
    simpa [mul_comm] using this
  have hcastpow : ∀ c : ℕ, ((c : AdjoinRoot f)) ^ r = c := by
    intro c
    have h1 : ((c : ZMod r)) ^ r = c := ZMod.pow_card _
    have := congrArg (algebraMap (ZMod r) (AdjoinRoot f)) h1
    rw [map_pow, map_natCast] at this
    exact this
  have hr1 : 1 ≤ r := hr.out.one_lt.le
  -- γ is a unit with inverse Qi β^2
  have hinv : γ * ((Qi : AdjoinRoot f) * β ^ 2) = 1 := by
    have : γ * ((Qi : AdjoinRoot f) * β ^ 2) = ((Qi : AdjoinRoot f) * Q) ^ 2 := by
      simp only [γ]; rw [← hαβ]; ring
    rw [this, hQiA, one_pow]
  -- the key dichotomy for α ^ r
  have hcase : α ^ r = α ∨ α ^ r = β := by
    by_cases hsplit : ∃ c : ZMod r, f.IsRoot c
    · obtain ⟨c, hc⟩ := hsplit
      left
      have hc' : c ^ 2 - (P : ZMod r) * c + (Q : ZMod r) = 0 := by
        simp only [f, IsRoot, eval_add, eval_mul, eval_C, eval_pow, eval_X, one_mul] at hc
        linear_combination hc
      set c2 : ZMod r := (P : ZMod r) - c
      have hd : c - c2 ≠ 0 := by
        intro h0
        apply hD
        have : (c - c2) ^ 2 = ((P * P : ℕ) : ZMod r) - 4 * (Q : ZMod r) := by
          simp only [c2]; push_cast; linear_combination 4 * hc'
        rw [← this, h0]; ring
      set d : AdjoinRoot f := algebraMap (ZMod r) (AdjoinRoot f) (c - c2)⁻¹
      set cc : AdjoinRoot f := algebraMap (ZMod r) (AdjoinRoot f) c
      set cc2 : AdjoinRoot f := algebraMap (ZMod r) (AdjoinRoot f) c2
      have hdd : (cc - cc2) * d = 1 := by
        simp only [cc, cc2, d, ← map_sub, ← map_mul, mul_inv_cancel₀ hd, map_one]
      have hcc2 : cc2 = (P : AdjoinRoot f) - cc := by simp [cc2, cc, c2]
      have hcQ : cc * cc2 = Q := by
        have : c * c2 = (Q : ZMod r) := by simp only [c2]; linear_combination -hc'
        have := congrArg (algebraMap (ZMod r) (AdjoinRoot f)) this
        simpa [cc, cc2] using this
      have hprod : (α - cc) * (α - cc2) = 0 := by
        rw [hcc2]; rw [hcc2] at hcQ; linear_combination hroot + hcQ
      set e1 : AdjoinRoot f := (α - cc2) * d
      set e2 : AdjoinRoot f := (cc - α) * d
      have hsum : e1 + e2 = 1 := by simp only [e1, e2]; linear_combination hdd
      have hprod12 : e1 * e2 = 0 := by
        simp only [e1, e2]; linear_combination (-(d ^ 2)) * hprod
      have hid1 : IsIdempotentElem e1 := by
        unfold IsIdempotentElem
        linear_combination e1 * hsum - hprod12
      have hid2 : IsIdempotentElem e2 := by
        unfold IsIdempotentElem
        linear_combination e2 * hsum - hprod12
      have hαe : α = cc * e1 + cc2 * e2 := by
        simp only [e1, e2]; linear_combination (-α) * hdd
      have hccr : cc ^ r = cc := by
        simp only [cc, ← map_pow, ZMod.pow_card]
      have hcc2r : cc2 ^ r = cc2 := by
        simp only [cc2, ← map_pow, ZMod.pow_card]
      have he1r : e1 ^ r = e1 := by
        have := hid1.pow_succ_eq (r - 1); rwa [Nat.sub_add_cancel hr1] at this
      have he2r : e2 ^ r = e2 := by
        have := hid2.pow_succ_eq (r - 1); rwa [Nat.sub_add_cancel hr1] at this
      clear_value e1 e2 cc cc2 d
      calc α ^ r = (cc * e1 + cc2 * e2) ^ r := by rw [← hαe]
        _ = (cc * e1) ^ r + (cc2 * e2) ^ r := add_pow_char _ _ _
        _ = cc ^ r * e1 ^ r + cc2 ^ r * e2 ^ r := by rw [mul_pow, mul_pow]
        _ = α := by rw [hccr, hcc2r, he1r, he2r, ← hαe]
    · push_neg at hsplit
      have hirr : Irreducible f :=
        irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) hsplit
      have : Fact (Irreducible f) := ⟨hirr⟩
      have hfr : (α ^ r) ^ 2 - (P : AdjoinRoot f) * α ^ r + (Q : AdjoinRoot f) = 0 := by
        have h := congrArg (frobenius (AdjoinRoot f) r) hroot
        simp only [map_add, map_sub, map_mul, map_pow, map_natCast, frobenius_def, map_zero] at h
        linear_combination h
      have hfac : (α ^ r - α) * (α ^ r - β) = 0 := by
        rw [hβ]; linear_combination hfr - hroot
      rcases mul_eq_zero.mp hfac with h | h
      · left; exact sub_eq_zero.mp h
      · right; exact sub_eq_zero.mp h
  rcases hcase with h | h
  · left
    have hγr : γ ^ r = γ := by
      simp only [γ]; rw [mul_pow, hcastpow, ← pow_mul, mul_comm 2 r, pow_mul, h]
    clear_value γ β
    have h1 : γ ^ (r - 1) * γ = γ := by
      rw [← pow_succ, Nat.sub_add_cancel hr1, hγr]
    calc γ ^ (r - 1) = γ ^ (r - 1) * (γ * ((Qi : AdjoinRoot f) * β ^ 2)) := by
          rw [hinv, mul_one]
      _ = (γ ^ (r - 1) * γ) * ((Qi : AdjoinRoot f) * β ^ 2) := by ring
      _ = 1 := by rw [h1, hinv]
  · right
    have hγr : γ ^ r = (Qi : AdjoinRoot f) * β ^ 2 := by
      simp only [γ]; rw [mul_pow, hcastpow, ← pow_mul, mul_comm 2 r, pow_mul, h]
    clear_value γ β
    rw [pow_succ, hγr, mul_comm]
    exact hinv


/-- In `AdjoinRoot f` for the monic quadratic `f`, the elements `1` and `α` are
linearly independent over `ZMod r`. -/
theorem lin_indep (r : ℕ) [Fact r.Prime] (P Q : ℕ) (a b : ZMod r)
    (h : algebraMap (ZMod r) (AdjoinRoot (C 1 * X ^ 2 + C (-(P : ZMod r)) * X + C (Q : ZMod r))) a +
      algebraMap (ZMod r) (AdjoinRoot (C 1 * X ^ 2 + C (-(P : ZMod r)) * X + C (Q : ZMod r))) b *
        AdjoinRoot.root (C 1 * X ^ 2 + C (-(P : ZMod r)) * X + C (Q : ZMod r)) = 0) :
    a = 0 ∧ b = 0 := by
  set f : (ZMod r)[X] := C 1 * X ^ 2 + C (-(P : ZMod r)) * X + C (Q : ZMod r) with hf
  have hdeg : f.natDegree = 2 := natDegree_quadratic one_ne_zero
  have hmk : AdjoinRoot.mk f (C b * X + C a) = 0 := by
    rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X, ← h]
    simp only [AdjoinRoot.algebraMap_eq]; ring
  have hdvd := AdjoinRoot.mk_eq_zero.mp hmk
  have hz : C b * X + C a = 0 := by
    apply eq_zero_of_dvd_of_degree_lt hdvd
    have hf0 : f ≠ 0 := by intro h0; rw [h0] at hdeg; simp at hdeg
    rw [degree_eq_natDegree hf0, hdeg]
    calc (C b * X + C a).degree ≤ (1 : WithBot ℕ) := degree_linear_le
      _ < ((2 : ℕ) : WithBot ℕ) := by exact_mod_cast (by norm_num : (1 : ℕ) < 2)
  have h0 := congrArg (fun p => coeff p 0) hz
  have h1 := congrArg (fun p => coeff p 1) hz
  simp at h0 h1
  exact ⟨h0, h1⟩

/-- The N + 1 half: every prime factor `r` of `n` is `1` or `-1` modulo the
factored part `F2` of `n + 1`, given the Lucas conditions computed by the kernel. -/
theorem lucas_factor (n P Q nQ Qi : ℕ) (L : List (ℕ × ℕ)) (hn : 2 ≤ n) (hK : n + 1 < 2 ^ K)
    (hnQ : (nQ + Q) % n = 0) (hQi : Q * Qi % n = 1 % n)
    (hD : Nat.gcd (P * P + 4 * nQ) n = 1)
    (hc : chain 0 L = true) (hprimes : ∀ x ∈ L, x.1.Prime)
    (hF : (n + 1) % prodPow L = 0)
    (hfer : qpow K n P nQ (nQ * Qi % n, P * Qi % n) (n + 1) = (1 % n, 0))
    (hgcd : ∀ x ∈ L, Nat.gcd (Nat.gcd
      ((qpow K n P nQ (nQ * Qi % n, P * Qi % n) ((n + 1) / x.1)).1 + n - 1)
      (qpow K n P nQ (nQ * Qi % n, P * Qi % n) ((n + 1) / x.1)).2) n = 1)
    (r : ℕ) (hrp : r.Prime) (hrn : r ∣ n) :
    prodPow L ∣ r - 1 ∨ prodPow L ∣ r + 1 := by
  have : Fact r.Prime := ⟨hrp⟩
  have hnr : ((n : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff n r).mpr hrn
  have h1n : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
  have hnQr : ((nQ : ℕ) : ZMod r) = -(Q : ZMod r) := by
    have : ((nQ + Q : ℕ) : ZMod r) = 0 :=
      (ZMod.natCast_eq_zero_iff _ r).mpr (hrn.trans (Nat.dvd_of_mod_eq_zero hnQ))
    push_cast at this
    linear_combination this
  have hQi' : ((Q * Qi : ℕ) : ZMod r) = 1 := by
    rw [← cast_mod_of_zero hnr, hQi, h1n, Nat.cast_one]
  have hD' : ((P * P : ℕ) : ZMod r) - 4 * (Q : ZMod r) ≠ 0 := by
    intro h0
    have hz : ((P * P + 4 * nQ : ℕ) : ZMod r) = 0 := by
      push_cast; rw [hnQr]; push_cast at h0; linear_combination h0
    have hd := Nat.dvd_gcd ((ZMod.natCast_eq_zero_iff _ r).mp hz) hrn
    rw [hD] at hd
    exact hrp.one_lt.ne' (Nat.dvd_one.mp hd)
  have hfd := frob_dichotomy r P Q Qi hQi' hD'
  dsimp only at hfd
  set f : (ZMod r)[X] := C 1 * X ^ 2 + C (-(P : ZMod r)) * X + C (Q : ZMod r) with hf
  set α := AdjoinRoot.root f
  set γ : AdjoinRoot f := ((Qi : ℕ) : AdjoinRoot f) * α ^ 2
  have hroot : α ^ 2 = (P : AdjoinRoot f) * α - (Q : AdjoinRoot f) := by
    have h := AdjoinRoot.eval₂_root f
    simp only [f, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, eval₂_pow, eval₂_neg, eval₂_natCast,
      map_one, map_neg, map_natCast, one_mul] at h
    linear_combination h
  have hnA : ((n : ℕ) : AdjoinRoot f) = 0 := by
    rw [← map_natCast (algebraMap (ZMod r) (AdjoinRoot f)), hnr, map_zero]
  have hnQA : ((nQ : ℕ) : AdjoinRoot f) = -(Q : AdjoinRoot f) := by
    rw [← map_natCast (algebraMap (ZMod r) (AdjoinRoot f)), hnQr, map_neg, map_natCast]
  have hg : qval α (nQ * Qi % n, P * Qi % n) = γ := by
    simp only [qval, cast_mod_of_zero hnA, Nat.cast_mul, hnQA, γ]
    rw [hroot]; ring
  have hpow : ∀ e, e < 2 ^ K → qval α (qpow K n P nQ (nQ * Qi % n, P * Qi % n) e) = γ ^ e := by
    intro e he; rw [qpow_val hnA hroot hnQA K _ e he, hg]
  have hγ1 : γ ^ (n + 1) = 1 := by
    rw [← hpow _ hK, hfer]; simp [qval, h1n]
  have hne : ∀ x ∈ L, γ ^ ((n + 1) / x.1) ≠ 1 := by
    intro x hx h1
    have hle : (n + 1) / x.1 < 2 ^ K := lt_of_le_of_lt (Nat.div_le_self _ _) hK
    rw [← hpow _ hle] at h1
    set y := qpow K n P nQ (nQ * Qi % n, P * Qi % n) ((n + 1) / x.1)
    have hli := lin_indep r P Q ((y.1 : ZMod r) - 1) (y.2 : ZMod r) (by
      simp only [qval] at h1
      simp only [map_sub, map_natCast, map_one]
      linear_combination h1)
    have hd1 : r ∣ y.1 + n - 1 := by
      apply (ZMod.natCast_eq_zero_iff _ r).mp
      rw [Nat.cast_sub (by omega), Nat.cast_add, hnr]
      simpa [sub_eq_zero] using hli.1
    have hd2 : r ∣ y.2 := (ZMod.natCast_eq_zero_iff _ r).mp hli.2
    have hd := Nat.dvd_gcd (Nat.dvd_gcd hd1 hd2) hrn
    rw [hgcd x hx] at hd
    exact hrp.one_lt.ne' (Nat.dvd_one.mp hd)
  have hFo := prodPow_dvd_orderOf γ (n + 1) L hc hprimes (Nat.dvd_of_mod_eq_zero hF) hγ1 hne
  rcases hfd with h | h
  · left; exact hFo.trans (orderOf_dvd_of_pow_eq_one h)
  · right; exact hFo.trans (orderOf_dvd_of_pow_eq_one h)

/-- The combined N - 1 and N + 1 test. `F1 ∣ r - 1` for every prime factor `r`, and
`F2 ∣ r - 1` or `F2 ∣ r + 1`. If `n < lcm F1 F2 ^ 2`, a prime factor `r ≤ √n` must be
the residue `s0` below the lcm that is `1` modulo `F1` and `-1` modulo `F2`, and the
certificate checks that `s0` is not a proper factor. -/
theorem combined (n : ℕ) (F1 F2 s0 : ℕ) (hn : 2 ≤ n)
    (h1 : ∀ r, r.Prime → r ∣ n → F1 ∣ r - 1)
    (h2 : ∀ r, r.Prime → r ∣ n → F2 ∣ r - 1 ∨ F2 ∣ r + 1)
    (hL : n < Nat.lcm F1 F2 * Nat.lcm F1 F2) (hs0 : s0 < Nat.lcm F1 F2)
    (hs1 : s0 % F1 = 1 % F1) (hs2 : (s0 + 1) % F2 = 0)
    (hs3 : s0 < 2 ∨ n % s0 ≠ 0 ∨ n < s0 * s0) : n.Prime := by
  by_contra hnp
  set r := n.minFac
  have hrp : r.Prime := Nat.minFac_prime (by omega)
  have hrn : r ∣ n := Nat.minFac_dvd n
  have hrsq : r ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  have hr2 := hrp.two_le
  set M := Nat.lcm F1 F2
  have hrM : r < M := by
    by_contra h; push Not at h
    have : M * M ≤ r * r := Nat.mul_le_mul h h
    rw [pow_two] at hrsq; omega
  have hF1 := h1 r hrp hrn
  rcases h2 r hrp hrn with h | h
  · have := Nat.le_of_dvd (by omega) (Nat.lcm_dvd hF1 h)
    omega
  · have m1 : r % F1 = s0 % F1 := by
      rw [hs1]; exact ((Nat.modEq_iff_dvd' (by omega)).mpr hF1).symm
    have m2 : r % F2 = s0 % F2 := by
      have a : (r + 1) % F2 = (s0 + 1) % F2 := by rw [hs2]; exact Nat.mod_eq_zero_of_dvd h
      exact Nat.ModEq.add_right_cancel' 1 a
    have hrs : r = s0 := by
      rcases le_total r s0 with hle | hle
      · have d1 : F1 ∣ s0 - r := (Nat.modEq_iff_dvd' hle).mp m1
        have d2 : F2 ∣ s0 - r := (Nat.modEq_iff_dvd' hle).mp m2
        have := Nat.lcm_dvd d1 d2
        rcases Nat.eq_zero_or_pos (s0 - r) with h0 | h0
        · omega
        · have := Nat.le_of_dvd h0 this; omega
      · have d1 : F1 ∣ r - s0 := (Nat.modEq_iff_dvd' hle).mp m1.symm
        have d2 : F2 ∣ r - s0 := (Nat.modEq_iff_dvd' hle).mp m2.symm
        have := Nat.lcm_dvd d1 d2
        rcases Nat.eq_zero_or_pos (r - s0) with h0 | h0
        · omega
        · have := Nat.le_of_dvd h0 this; omega
    rw [← hrs] at hs3
    rcases hs3 with h | h | h
    · omega
    · exact h (Nat.mod_eq_zero_of_dvd hrn)
    · rw [pow_two] at hrsq; omega


/-- A combined certificate: `(n, a, t, L1, P, Q, nQ, Qi, s0, L2)`. With `L2 = []` it is
the plain N - 1 certificate `(n, a, t, L1)`. Otherwise `a, L1` are the N - 1 data,
`P, Q` the Lucas pair, `nQ = -Q mod n`, `Qi = Q⁻¹ mod n`, `L2` the factored part of
`n + 1`, and `s0` the residue below `lcm F1 F2` that is `1 mod F1` and `-1 mod F2`. -/
abbrev Cert2 := ℕ × ℕ × ℕ × List (ℕ × ℕ) × ℕ × ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ)

/-- Primes of a factor list: certified earlier, or below `2 ^ 16` by trial division. -/
def primesOK (pr : List ℕ) (L : List (ℕ × ℕ)) : Bool :=
  L.all (fun x => pr.elem x.1 || (decide (x.1 < 65536) && LeanLab.primeB x.1))

theorem primesOK_sound (pr : List ℕ) (hpr : ∀ p ∈ pr, p.Prime) (L : List (ℕ × ℕ))
    (h : primesOK pr L = true) : ∀ x ∈ L, x.1.Prime := by
  intro x hx
  simp only [primesOK, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, List.elem_eq_mem,
    decide_eq_true_eq] at h
  rcases h x hx with h | h
  · exact hpr _ h
  · exact LeanLab.primeB_sound h.2

/-- Boolean check of the combined N - 1 and N + 1 conditions. -/
def combOK (pr : List ℕ) : Cert2 → Bool
  | (n, a, _, L1, P, Q, nQ, Qi, s0, L2) =>
    decide (2 ≤ n) && decide (n + 1 < 2 ^ K) && chain 0 L1 &&
      ((n - 1) % prodPow L1 == 0) && primesOK pr L1 &&
      (pm K a (n - 1) n == 1 % n) &&
      L1.all (fun x => Nat.gcd (pm K a ((n - 1) / x.1) n + n - 1) n == 1) &&
      chain 0 L2 && ((n + 1) % prodPow L2 == 0) && primesOK pr L2 &&
      ((nQ + Q) % n == 0) && (Q * Qi % n == 1 % n) && (Nat.gcd (P * P + 4 * nQ) n == 1) &&
      decide (qpow K n P nQ (nQ * Qi % n, P * Qi % n) (n + 1) = (1 % n, 0)) &&
      L2.all (fun x => Nat.gcd (Nat.gcd
        ((qpow K n P nQ (nQ * Qi % n, P * Qi % n) ((n + 1) / x.1)).1 + n - 1)
        (qpow K n P nQ (nQ * Qi % n, P * Qi % n) ((n + 1) / x.1)).2) n == 1) &&
      decide (n < Nat.lcm (prodPow L1) (prodPow L2) * Nat.lcm (prodPow L1) (prodPow L2)) &&
      decide (s0 < Nat.lcm (prodPow L1) (prodPow L2)) &&
      (s0 % prodPow L1 == 1 % prodPow L1) && ((s0 + 1) % prodPow L2 == 0) &&
      (decide (s0 < 2) || n % s0 != 0 || decide (n < s0 * s0))

/-- Boolean check of one combined certificate. -/
def certOK2 (pr : List ℕ) (c : Cert2) : Bool :=
  (c.2.2.2.2.2.2.2.2.2.isEmpty && certOK pr (c.1, c.2.1, c.2.2.1, c.2.2.2.1)) || combOK pr c

theorem combOK_sound (pr : List ℕ) (hpr : ∀ p ∈ pr, p.Prime) (c : Cert2)
    (h : combOK pr c = true) : c.1.Prime := by
  obtain ⟨n, a, t, L1, P, Q, nQ, Qi, s0, L2⟩ := c
  simp only [combOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h2, hK⟩, hc1⟩, hF1⟩, hp1⟩, hfer1⟩, hgcd1⟩, hc2⟩, hF2⟩, hp2⟩, hnQ⟩, hQi⟩, hD⟩, hfer2⟩, hgcd2⟩, hL⟩, hs0⟩, hs1⟩, hs2⟩, hs3⟩ := h
  have hK' : n < 2 ^ K := by omega
  refine combined n (prodPow L1) (prodPow L2) s0 h2
    (pock_factor n a L1 h2 hK' hc1 (primesOK_sound pr hpr L1 hp1) hF1 hfer1 hgcd1)
    (lucas_factor n P Q nQ Qi L2 h2 hK hnQ hQi hD hc2 (primesOK_sound pr hpr L2 hp2) hF2
      hfer2 hgcd2) hL hs0 hs1 hs2 ?_
  rcases hs3 with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem certOK2_sound (pr : List ℕ) (hpr : ∀ p ∈ pr, p.Prime) (c : Cert2)
    (h : certOK2 pr c = true) : c.1.Prime := by
  simp only [certOK2, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨_, h⟩ | h
  · exact certOK_sound pr hpr _ h
  · exact combOK_sound pr hpr c h

/-- A chain of combined certificates, each allowed to use the earlier ones. -/
def chainOK2 : List ℕ → List Cert2 → Bool
  | _, [] => true
  | pr, c :: cs => certOK2 pr c && chainOK2 (c.1 :: pr) cs

theorem chainOK2_sound : ∀ (cs : List Cert2) (pr : List ℕ), (∀ p ∈ pr, p.Prime) →
    chainOK2 pr cs = true → ∀ c ∈ cs, c.1.Prime
  | [], _, _, _, c, hc => by simp at hc
  | d :: cs, pr, hpr, h, c, hc => by
    simp only [chainOK2, Bool.and_eq_true] at h
    have hd := certOK2_sound pr hpr d h.1
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hd
    · exact chainOK2_sound cs (d.1 :: pr)
        (fun p hp => by
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hd
          · exact hpr p hp) h.2 c hc

/-- A nonempty checked chain of combined certificates. -/
def chainB2 (ch : List Cert2) : Bool := !ch.isEmpty && chainOK2 [] ch

/-- The number certified last by a combined chain, or 0 for the empty chain. -/
def lastP2 (ch : List Cert2) : ℕ := (ch.getLast?.map Prod.fst).getD 0

theorem lastP2_prime (ch : List Cert2) (h : chainB2 ch = true) : (lastP2 ch).Prime := by
  simp only [chainB2, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨hne, h⟩ := h
  have hmem := List.getLast_mem hne
  have := chainOK2_sound ch [] (by simp) h _ hmem
  simpa [lastP2, List.getLast?_eq_some_getLast hne] using this

/-- Every number of `l` is prime when `l` lists the last numbers of checked chains. -/
theorem primes_of_chains2 (C : List (List Cert2)) (l : List ℕ) (hl : C.map lastP2 = l)
    (hC : C.all chainB2 = true) : ∀ q ∈ l, q.Prime := by
  intro q hq
  rw [← hl] at hq
  obtain ⟨ch, hch, rfl⟩ := List.mem_map.mp hq
  exact lastP2_prime ch (List.all_eq_true.mp hC ch hch)

#print axioms primes_of_chains2

end LeanLab.DtRS1998.PocklingtonB7
