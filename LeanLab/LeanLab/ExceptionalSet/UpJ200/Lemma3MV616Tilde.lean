import LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Integral
import LeanLab.ExceptionalSet.UpJ200.Lemma2MV.Lemma55Termwise
import LeanLab.PNTPort.Vinogradov.SingPos
import LeanLab.PNTPort.Vinogradov.SingSeries

/-!
# Proof of the LEAF `mv_616_tilde` of `Lemma3MV617Integral`

Burst burst-20261122, step mv616_tilde, Claude cloud session S112.

Source P0015, Montgomery and Vaughan 1975, page 365 display (6.1̃6), proved there "by Lemma 5.1
and (5.2)". With `q = r̃ m`, Lemma 5.1 gives `τ(χ̃χ₀) = μ(m) χ̃(m) τ(χ̃)`, and `τ(χ̃)² = χ̃(-1) r̃`
for the real primitive `χ̃`. So the term of `q = r̃ m` vanishes unless `(m, r̃) = 1`, and then, by
multiplicativity of `φ` and of the Ramanujan sum, it is `χ̃(-1) r̃ c_{r̃}(-n) φ(r̃)⁻²` times the
non exceptional term `μ(m)² c_m(-n) φ(m)⁻²` of (6.4). Then (5.2) evaluates `c_{r̃}(-n)` and the
Euler product over `p ∤ r̃` gives the rest of P0082 display (12).

All steps PROVED, sorry free:
* `mv616_tau_induced`: Lemma 5.1 of P0015, page 358, from `Lemma2MVSplit.mv_lemma52`.
* `mv616_gauss_sq`: `τ(χ̃)² = χ̃(-1) r̃`, page 365 before (6.1̃6).
* `mv616_ramanujan_mul`: multiplicativity of `c_q`, used at (6.1̃6).
* `mv616_ramanujan_eval`: (5.2) of P0015, `c_q(n) = μ(q/(q,n)) φ(q) / φ(q/(q,n))`.
* `mv616_euler_coprime`: the Euler product of (6.1̃6) over `p ∤ r̃`.
* `mv_616_tilde_proved`, the type twin of `Lemma3MV617Integral.mv_616_tilde`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Lemma3MV616Tilde

open Finset
open LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Integral
  (tauInd excWeight tauInd_of_not_dvd tauInd_zero)
open LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit (ramanujan mainWeight mainWeight_zero rem66_cchi
  mv_lemma52 mv_lemma54_of rem66_cchi_one_eq_gaussSum)
open LeanLab.HeathBrown1985 (gm gm_one gm_mul gm_zero gm_eq summable_abs_gm vloc_dvd vloc_not_dvd)
open LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082 (twistedSing singFactor)

/-- PROVED, formerly LEAF: P0015 Lemma 5.1, page 358, class MEDIUM, from the lab's proved
`Lemma2MVSplit.mv_lemma52`. For `χ̃` primitive mod `r̃` and `r̃ ∣ q`,
`q ≠ 0`, the Gauss sum of the induced character mod `q` is `τ(χ̃χ₀) = μ(q/r̃) χ̃(q/r̃) τ(χ̃)`. -/
theorem mv616_tau_induced : ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive →
    ∀ q : ℕ, r ∣ q → q ≠ 0 →
      tauInd χ q = ((ArithmeticFunction.moebius (q / r) : ℤ) : ℂ) * χ ((q / r : ℕ) : ZMod r) *
        gaussSum χ ZMod.stdAddChar := by
  intro r _ χ hprim q hrq hq
  have : NeZero q := ⟨hq⟩
  have h := mv_lemma52 r q χ hrq (Nat.one_le_iff_ne_zero.mpr hq) hprim
  rw [rem66_cchi_one_eq_gaussSum, rem66_cchi_one_eq_gaussSum] at h
  unfold tauInd
  rw [dif_pos ⟨hrq, hq⟩]
  exact h


/-- PROVED, formerly LEAF: P0015 page 365, the step before (6.1̃6), class MEDIUM. For a real
primitive character `χ̃` mod `r̃`, `τ(χ̃)² = χ̃(-1) r̃`, from `τ(χ̃) τ(χ̃̄) = χ̃(-1) r̃` and `χ̃̄ = χ̃`.
The norm `|τ(χ̃)|² = r̃` comes from the energy identity of `DERZ1997.Decomp1529c.gaussSum_norm_le`,
with equality since `τ(χ̃, e_a) = 0` for nonunits `a` when `χ̃` is primitive. -/
theorem mv616_gauss_sq : ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive →
    χ ^ 2 = 1 → gaussSum χ ZMod.stdAddChar ^ 2 = χ (-1) * (r : ℂ) := by
  classical
  intro q _ χ hprim hsq
  let e136 : AddChar (ZMod q) ℂ := ZMod.stdAddChar
  let G : ZMod q → ℂ := fun a => gaussSum χ (e136.mulShift a)
  have hortho (t : ZMod q) : ∑ a : ZMod q, e136 (t * a) = if t = 0 then (q : ℂ) else 0 := by
    by_cases ht : t = 0
    · simp [ht, e136]
    · rw [ite_eq_right ht]
      exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q ht)
  have hstar (x : ZMod q) : star (e136 x) = e136 (-x) := by
    simpa [e136, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv] using
      (Complex.inv_eq_conj (Circle.norm_coe (ZMod.toCircle x))).symm
  have henergy : (∑ a : ZMod q, G a * star (G a)) =
      q * ∑ x : ZMod q, χ x * star (χ x) := by
    simp only [G, gaussSum, star_sum, star_mul, AddChar.mulShift_apply]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    have hterm (a y : ZMod q) :
        χ x * e136 (a * x) * (star (e136 (a * y)) * star (χ y)) =
          (χ x * star (χ y)) * e136 ((x - y) * a) := by
      rw [hstar]
      calc
        _ = (χ x * star (χ y)) * (e136 (a * x) * e136 (-(a * y))) := by ring
        _ = _ := by rw [← AddChar.map_add_eq_mul]; congr 2 <;> ring
    simp_rw [hterm]
    simp_rw [← Finset.mul_sum, hortho]
    simp [sub_eq_zero, mul_ite]
    ring
  have hone (x : ZMod q) : χ x * star (χ x) = (1 : DirichletCharacter ℂ q) x := by
    by_cases hx : IsUnit x
    · change χ x * (starRingEnd ℂ) (χ x) = _
      rw [Complex.mul_conj', ← hx.unit_spec, χ.unit_norm_eq_one]
      simp [MulChar.one_apply hx]
    · simp [MulChar.map_nonunit _ hx]
  have hchars : (∑ x : ZMod q, χ x * star (χ x)) = (q.totient : ℂ) := by
    simp_rw [hone]
    rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  have hinv : χ⁻¹ = χ := by
    have : χ * χ = 1 := by rw [← pow_two, hsq]
    exact inv_eq_of_mul_eq_one_right this
  set τ := gaussSum χ e136 with hτ
  have hG (a : ZMod q) : G a * star (G a) = (1 : DirichletCharacter ℂ q) a * (τ * star τ) := by
    dsimp only [G]
    rw [gaussSum_mulShift_of_isPrimitive _ hprim, hinv, star_mul, ← hone]
    ring
  simp_rw [hG] at henergy
  rw [← Finset.sum_mul, hchars] at henergy
  have htot : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hss : τ * star τ = q := by
    have := henergy
    rw [show (∑ x : ZMod q, (1 : DirichletCharacter ℂ q) x) = (q.totient : ℂ) by
      rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]] at this
    apply mul_left_cancel₀ htot
    linear_combination this
  have hst : star τ = χ (-1) * τ := by
    rw [hτ, star_gaussSum_eq, hinv]
    have : e136⁻¹ = e136.mulShift (-1) := by
      ext x; simp [AddChar.mulShift_apply]
    rw [this, gaussSum_mulShift_of_isPrimitive _ hprim, hinv]
  have h2 : χ (-1) * χ (-1) = 1 := by
    have h := congrArg (fun ψ : DirichletCharacter ℂ q => ψ (-1)) hsq
    simp only [pow_two, MulChar.mul_apply] at h
    rw [h, MulChar.one_apply isUnit_one.neg]
  rw [hst] at hss
  linear_combination χ (-1) * hss - τ ^ 2 * h2


/-- Bridge: `c_q(-n)` written with `eC` is the lab's real Ramanujan sum
`HeathBrown1985.ramanujan q n = Σ_{d ∣ (n,q)} d μ(q/d)`. PROVED, by conjugation and
`PNTPort.Vinogradov.ramanujan_sum`. -/
theorem ramanujan_neg_eq_hb (q : ℕ) (hq : 1 ≤ q) (n : ℕ) :
    ramanujan q (-(n : ℤ)) = ((LeanLab.HeathBrown1985.ramanujan q n : ℝ) : ℂ) := by
  have h := LeanLab.PNTPort.Vinogradov.ramanujan_sum hq n
  have hc : ramanujan q (-(n : ℤ)) = starRingEnd ℂ
      (∑ r ∈ (range q).filter (fun r => Nat.Coprime r q),
        LeanLab.PNTPort.LargeSieve.e (n * r / q)) := by
    unfold ramanujan
    rw [map_sum]
    refine sum_congr rfl fun h _ => ?_
    unfold LeanLab.ExceptionalSet.U1539.eC LeanLab.PNTPort.LargeSieve.e
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [hc, h, Complex.conj_ofReal]

/-- PROVED, formerly LEAF: multiplicativity of the Ramanujan sum used at P0015 display (6.1̃6),
page 365, class EASY: `c_{ab}(-n) = c_a(-n) c_b(-n)` for `(a, b) = 1`, `a, b ≥ 1`, from the
multiplicative function `PNTPort.Vinogradov.cR`. -/
theorem mv616_ramanujan_mul : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → Nat.Coprime a b → ∀ n : ℕ,
    ramanujan (a * b) (-(n : ℤ)) = ramanujan a (-(n : ℤ)) * ramanujan b (-(n : ℤ)) := by
  intro a b ha hb hab n
  have hab1 : 1 ≤ a * b := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [ramanujan_neg_eq_hb _ hab1, ramanujan_neg_eq_hb _ ha, ramanujan_neg_eq_hb _ hb]
  have h := (LeanLab.PNTPort.Vinogradov.cR_mult n).map_mul_of_coprime hab
  rw [LeanLab.PNTPort.Vinogradov.cR_apply hab1 n, LeanLab.PNTPort.Vinogradov.cR_apply ha n,
    LeanLab.PNTPort.Vinogradov.cR_apply hb n] at h
  rw [h]; push_cast; ring

/-- The Ramanujan sum is the twisted sum of the principal character, P0015 display (2.1). PROVED. -/
theorem cchi_one_eq_ramanujan (q : ℕ) (m : ℤ) :
    rem66_cchi (1 : DirichletCharacter ℂ q) m = ramanujan q m := by
  unfold rem66_cchi ramanujan
  rw [sum_filter]
  refine sum_congr rfl fun h _ => ?_
  by_cases hc : Nat.Coprime h q
  · rw [if_pos hc, MulChar.one_apply ((ZMod.isUnit_iff_coprime h q).mpr hc), one_mul]
  · rw [if_neg hc, MulChar.map_nonunit _ (fun hu => hc ((ZMod.isUnit_iff_coprime h q).mp hu)),
      zero_mul]

theorem level_one_apply {c : ℕ} (hc : c = 1) (ψ : DirichletCharacter ℂ c) (x : ZMod c) :
    ψ x = 1 := by
  subst hc
  rw [Subsingleton.elim x 1, map_one]

theorem cchi_level_one {c : ℕ} (hc : c = 1) (ψ : DirichletCharacter ℂ c) :
    rem66_cchi ψ 1 = 1 := by
  subst hc
  unfold rem66_cchi
  simp [level_one_apply rfl, LeanLab.ExceptionalSet.U1539.eC]

/-- PROVED, formerly LEAF: P0015 display (5.2), page 358, class MEDIUM, from the lab's proved
Lemma 5.4 `Lemma2MVSplit.mv_lemma54_of` at the principal character, conductor one: for `q ≥ 1`,
`c_q(-n) = μ(q/(q,n)) φ(q) φ(q/(q,n))⁻¹`. -/
theorem mv616_ramanujan_eval : ∀ q : ℕ, 1 ≤ q → ∀ n : ℕ,
    ramanujan q (-(n : ℤ)) =
      ((ArithmeticFunction.moebius (q / Int.gcd (n : ℤ) q) : ℤ) : ℂ) * (q.totient : ℂ) /
        ((q / Int.gcd (n : ℤ) q).totient : ℂ) := by
  intro q hq n
  have h := (mv_lemma54_of mv_lemma52 q (1 : DirichletCharacter ℂ q) hq (-(n : ℤ))).2
  have hg : Nat.gcd q (-(n : ℤ)).natAbs = Int.gcd (n : ℤ) q := by
    rw [Int.natAbs_neg, Int.natAbs_natCast, Int.gcd_natCast_natCast, Nat.gcd_comm]
  rw [← cchi_one_eq_ramanujan]
  have : NeZero q := ⟨by omega⟩
  have hc : (1 : DirichletCharacter ℂ q).conductor = 1 := DirichletCharacter.conductor_one
  rw [h (by rw [hc]; exact one_dvd _)]
  rw [level_one_apply hc, level_one_apply hc, cchi_level_one hc, hg]
  rw [hc, Nat.div_one]
  ring


/-- PROVED, formerly LEAF: the Euler product of P0015 display (6.1̃6), page 365, class MEDIUM,
by Mathlib's `EulerProduct.eulerProduct_hasProd` as in `HeathBrown1985.hasSum_gm`. For `n ≥ 1` the
series `Σ_{(m, r̃) = 1} μ(m)² c_m(-n) φ(m)⁻²` converges absolutely to
`∏_{p ∤ r̃, p ∤ n} (1 - (p-1)⁻²) ∏_{p ∤ r̃, p ∣ n} (1 + (p-1)⁻¹)`, as for (6.16) with the primes
dividing `r̃` removed. -/
theorem mv616_euler_coprime : ∀ r : ℕ, 1 ≤ r → ∀ n : ℕ, 1 ≤ n →
    Summable (fun m : ℕ => ‖if Nat.Coprime m r then mainWeight m n else 0‖) ∧
      HasSum (fun m : ℕ => if Nat.Coprime m r then mainWeight m n else 0)
        (((∏' p : Nat.Primes, (if (p : ℕ) ∣ r then 1 else singFactor (n : ℤ) p) : ℝ)) : ℂ) := by
  intro r hr n hn
  set f : ℕ → ℝ := fun m => if Nat.Coprime m r then gm n m else 0 with hfdef
  have hmw : ∀ m, mainWeight m n = ((gm n m : ℝ) : ℂ) := by
    intro m
    unfold mainWeight ramanujan
    exact LeanLab.ExceptionalSet.UpJ200.Lemma2MV.sing616_weight_eq m n
  have hfc : (fun m : ℕ => if Nat.Coprime m r then mainWeight m n else 0) =
      fun m => ((f m : ℝ) : ℂ) := by
    funext m; simp only [hfdef, hmw]; split_ifs <;> simp
  have hf1 : f 1 = 1 := by simp [hfdef, gm_one]
  have hfmul : ∀ {a b : ℕ}, Nat.Coprime a b → f (a * b) = f a * f b := by
    intro a b hab
    simp only [hfdef, Nat.coprime_mul_iff_left, gm_mul n hab]
    split_ifs <;> simp_all
  have hfle : ∀ m, ‖f m‖ ≤ ‖gm n m‖ := by
    intro m; simp only [hfdef]; split_ifs <;> simp
  have hsum : Summable (fun m => ‖f m‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hfle (summable_abs_gm n hn)
  have hf0 : f 0 = 0 := by simp [hfdef, gm_zero]
  have hE := EulerProduct.eulerProduct_hasProd (f := f) hf1 (fun hab => hfmul hab) hsum hf0
  have hloc : (fun p : Nat.Primes => ∑' e, f ((p : ℕ) ^ e)) =
      fun p : Nat.Primes => (if (p : ℕ) ∣ r then 1 else singFactor (n : ℤ) p) := by
    funext p
    have hp := p.2
    rw [tsum_eq_sum (s := range 2)]
    · rw [sum_range_succ, sum_range_succ, sum_range_zero, pow_zero, pow_one, zero_add, hf1]
      by_cases hd : (p : ℕ) ∣ r
      · have hnc : ¬ Nat.Coprime (p : ℕ) r := fun hc =>
          hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc hd)
        simp [hfdef, hnc, hd]
      · have hc : Nat.Coprime (p : ℕ) r := (Nat.Prime.coprime_iff_not_dvd hp).mpr hd
        simp only [hfdef, if_pos hc, if_neg hd]
        rw [gm_eq, if_pos hp.prime.squarefree, Nat.Prime.primeFactors hp, prod_singleton]
        unfold singFactor
        have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
        have hne : (p : ℝ) - 1 ≠ 0 := by linarith
        by_cases hpn : (p : ℕ) ∣ n
        · rw [vloc_dvd hp hpn, if_pos (Int.natCast_dvd_natCast.mpr hpn)]
        · rw [vloc_not_dvd hp hpn, if_neg (fun h => hpn (Int.natCast_dvd_natCast.mp h))]
          ring
    · intro e he
      simp only [mem_range, not_lt] at he
      simp only [hfdef]
      split_ifs
      · rw [gm_eq, if_neg]
        intro hsq
        have hd : (p : ℕ) * p ∣ (p : ℕ) ^ e := by
          rw [← pow_two]; exact pow_dvd_pow _ he
        exact hp.not_isUnit (hsq p hd)
      · rfl
  rw [hloc] at hE
  refine ⟨?_, ?_⟩
  · convert hsum using 2 with m
    rw [show (if Nat.Coprime m r then mainWeight m n else 0) = ((f m : ℝ) : ℂ) from
      congrFun hfc m, Complex.norm_real]
  · rw [hfc, hE.tprod_eq, Complex.hasSum_ofReal]
    exact hsum.of_norm.hasSum


/-- `χ̃(-1)` is real for a real character, so it equals its real part. PROVED. -/
theorem chi_neg_one_re {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hsq : χ ^ 2 = 1) :
    (((χ (-1)).re : ℝ) : ℂ) = χ (-1) := by
  have h2 : χ (-1) * χ (-1) = 1 := by
    have h := congrArg (fun ψ : DirichletCharacter ℂ r => ψ (-1)) hsq
    simp only [pow_two, MulChar.mul_apply] at h
    rw [h, MulChar.one_apply isUnit_one.neg]
  rcases mul_self_eq_one_iff.mp h2 with h | h <;> rw [h] <;> simp

/-- The term of `q = r̃ m` in (6.1̃6), by Lemma 5.1, `τ(χ̃)² = χ̃(-1) r̃`, multiplicativity and
(5.2). PROVED from the leaves. -/
theorem excWeight_mul (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive)
    (hsq : χ ^ 2 = 1) (n m : ℕ) :
    excWeight χ (r * m) n =
      (χ (-1) * ((ArithmeticFunction.moebius (r / Int.gcd (n : ℤ) r) : ℤ) : ℂ) *
        ((r : ℂ) / ((r.totient : ℂ) * ((r / Int.gcd (n : ℤ) r).totient : ℂ)))) *
      (if Nat.Coprime m r then mainWeight m n else 0) := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [excWeight, tauInd_zero, mainWeight_zero]
  have hq : r * m ≠ 0 := by positivity
  have hdiv : r * m / r = m := Nat.mul_div_cancel_left m hr
  have htau := mv616_tau_induced r χ hprim (r * m) (dvd_mul_right r m) hq
  rw [hdiv] at htau
  unfold excWeight
  rw [htau]
  by_cases hc : Nat.Coprime m r
  · rw [if_pos hc]
    have hχm : χ (m : ZMod r) ^ 2 = 1 := by
      have h := congrArg (fun ψ : DirichletCharacter ℂ r => ψ (m : ZMod r)) hsq
      simp only [MulChar.pow_apply' χ two_ne_zero] at h
      rw [h, MulChar.one_apply ((ZMod.isUnit_iff_coprime m r).mpr hc)]
    have hG := mv616_gauss_sq r χ hprim hsq
    have hmul := mv616_ramanujan_mul r m hr hm hc.symm n
    have hev := mv616_ramanujan_eval r hr n
    have htot : (r * m).totient = r.totient * m.totient := Nat.totient_mul hc.symm
    have hg : 0 < r / Int.gcd (n : ℤ) r := by
      have hd : Int.gcd (n : ℤ) r ∣ r := by
        rw [Int.gcd_natCast_natCast]; exact Nat.gcd_dvd_right n r
      apply Nat.div_pos (Nat.le_of_dvd hr hd)
      exact Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast hr.ne')
    have h1 : (r.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hr).ne'
    have h2 : (m.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hm).ne'
    have h3 : ((r / Int.gcd (n : ℤ) r).totient : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr hg).ne'
    unfold mainWeight
    rw [htot, hmul, hev]
    push_cast
    have e1 : (((ArithmeticFunction.moebius m : ℤ) : ℂ) * χ (m : ZMod r) *
        gaussSum χ ZMod.stdAddChar) ^ 2 =
        ((ArithmeticFunction.moebius m : ℤ) : ℂ) ^ 2 * χ (m : ZMod r) ^ 2 *
          gaussSum χ ZMod.stdAddChar ^ 2 := by ring
    rw [e1, hχm, hG]
    field_simp
  · simp only [hc, ↓reduceIte, mul_zero]
    have h0 : χ (m : ZMod r) = 0 :=
      MulChar.map_nonunit χ (fun h => hc ((ZMod.isUnit_iff_coprime m r).mp h))
    simp [h0]

/-- PROVED from the steps above: the type twin of `Lemma3MV617Integral.mv_616_tilde`, P0015
display (6.1̃6), page 365. -/
theorem mv_616_tilde_proved : type_of% @Lemma3MV617Integral.mv_616_tilde := by
  intro r hNZ χ hprim hsq hne n hn
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  set K : ℂ := χ (-1) * ((ArithmeticFunction.moebius (r / Int.gcd (n : ℤ) r) : ℤ) : ℂ) *
        ((r : ℂ) / ((r.totient : ℂ) * ((r / Int.gcd (n : ℤ) r).totient : ℂ))) with hK
  obtain ⟨hS, hH⟩ := mv616_euler_coprime r hr n hn
  have hinj : Function.Injective (fun m : ℕ => r * m) := fun a b h => Nat.eq_of_mul_eq_mul_left hr h
  have hzero : ∀ q ∉ Set.range (fun m : ℕ => r * m), excWeight χ q n = 0 := by
    intro q hq
    apply Lemma3MV617Integral.excWeight_of_tau
    apply tauInd_of_not_dvd
    rintro ⟨m, rfl⟩
    exact hq ⟨m, rfl⟩
  have hcomp : (fun q => excWeight χ q n) ∘ (fun m : ℕ => r * m) =
      fun m => K * (if Nat.Coprime m r then mainWeight m n else 0) := by
    funext m; exact excWeight_mul r χ hprim hsq n m
  refine ⟨?_, ?_⟩
  · rw [← hinj.summable_iff (f := fun q => ‖excWeight χ q n‖)
      (fun q hq => by simp [hzero q hq])]
    have : (fun q => ‖excWeight χ q n‖) ∘ (fun m : ℕ => r * m) =
        fun m => ‖K‖ * ‖if Nat.Coprime m r then mainWeight m n else 0‖ := by
      funext m; rw [Function.comp_apply, excWeight_mul r χ hprim hsq n m, norm_mul]
    rw [this]
    exact hS.mul_left _
  · rw [← hinj.hasSum_iff hzero, hcomp]
    have hval : K * (((∏' p : Nat.Primes, (if (p : ℕ) ∣ r then 1 else singFactor (n : ℤ) p) :
        ℝ)) : ℂ) = ((twistedSing χ (n : ℤ) : ℝ) : ℂ) := by
      unfold twistedSing
      push_cast
      rw [chi_neg_one_re χ hsq, hK]
    rw [← hval]
    exact hH.mul_left K

#print axioms mv_616_tilde_proved

end LeanLab.ExceptionalSet.UpJ200.Lemma3MV616Tilde
