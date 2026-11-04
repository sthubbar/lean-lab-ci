/-
Pointwise smooth truncation for Lemma 3.8, page 14 display 50.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp129b

namespace LeanLab.KumchevLiu2007.Task271a

open Real Complex Task129 Task129b
open scoped BigOperators
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 2000000

/-! ### The exponential `e(x) = exp(2 pi i x)` -/

private lemma ee_add_real (x y : ℝ) : U1534.ee (x + y) = U1534.ee x * U1534.ee y := by
  unfold U1534.ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma ee_int_add (u : ℝ) (k : ℤ) : U1534.ee (u + (k : ℝ)) = U1534.ee u := by
  unfold U1534.ee
  have h : ((2 : ℂ) * (π : ℂ) * I) * ((u + (k : ℝ) : ℝ) : ℂ)
      = ((2 : ℂ) * (π : ℂ) * I) * (u : ℂ) + (k : ℂ) * ((2 : ℂ) * (π : ℂ) * I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private lemma ee_nat_add_int (u : ℝ) (k : ℕ) : U1534.ee (u + (k : ℝ)) = U1534.ee u :=
  ee_int_add u (k : ℤ)


/-! ### Reduced residues and the Bezout form of CRT -/

private lemma crt_coprime {q r a1 a2 : ℕ} (hqr : q.Coprime r)
    (h1 : a1.Coprime q) (h2 : a2.Coprime r) : (a1 * r + a2 * q).Coprime (q * r) := by
  have hq' : q.Coprime (a1 * r) := Nat.Coprime.mul_right h1.symm hqr
  have hr' : r.Coprime (a2 * q) := Nat.Coprime.mul_right h2.symm hqr.symm
  have hqc : (a1 * r + a2 * q).Coprime q := by
    rw [Nat.coprime_comm]
    exact (Nat.coprime_add_mul_right_right q (a1 * r) a2).mpr hq'
  have hrc : (a1 * r + a2 * q).Coprime r := by
    rw [Nat.coprime_comm]
    rw [show a1 * r + a2 * q = a2 * q + a1 * r from by ring]
    exact (Nat.coprime_add_mul_right_right r (a2 * q) a1).mpr hr'
  exact Nat.Coprime.mul_right hqc hrc

private lemma coprime_of_mod {x n : ℕ} (h : x.Coprime n) : (x % n).Coprime n := by
  rw [Nat.coprime_iff_gcd_eq_one] at *
  rw [← Nat.gcd_rec n x, Nat.gcd_comm n x]
  exact h

private lemma crt_image_mem {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hqr : q.Coprime r)
    {p : ℕ × ℕ}
    (hp : p ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) ×ˢ
        (Finset.range r).filter (fun a => Nat.Coprime a r)) :
    (p.1 * r + p.2 * q) % (q * r) ∈
      (Finset.range (q * r)).filter (fun a => Nat.Coprime a (q * r)) := by
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  obtain ⟨-, h1⟩ := Finset.mem_filter.mp hp1
  obtain ⟨-, h2⟩ := Finset.mem_filter.mp hp2
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.mod_lt _ (Nat.mul_pos hq hr)),
      coprime_of_mod (crt_coprime hqr h1 h2)⟩

private lemma crt_injOn {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hqr : q.Coprime r) :
    Set.InjOn (fun p : ℕ × ℕ => (p.1 * r + p.2 * q) % (q * r))
      ↑((Finset.range q).filter (fun a => Nat.Coprime a q) ×ˢ
        (Finset.range r).filter (fun a => Nat.Coprime a r)) := by
  intro p hp p' hp' hpp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hp)
  obtain ⟨hp1', hp2'⟩ := Finset.mem_product.mp (Finset.mem_coe.mp hp')
  have hb1 : p.1 < q := Finset.mem_range.mp (Finset.mem_filter.mp hp1).1
  have hb2 : p.2 < r := Finset.mem_range.mp (Finset.mem_filter.mp hp2).1
  have hb1' : p'.1 < q := Finset.mem_range.mp (Finset.mem_filter.mp hp1').1
  have hb2' : p'.2 < r := Finset.mem_range.mp (Finset.mem_filter.mp hp2').1
  have hmod : p.1 * r + p.2 * q ≡ p'.1 * r + p'.2 * q [MOD q * r] := hpp
  have hq' : p.1 * r + p.2 * q ≡ p'.1 * r + p'.2 * q [MOD q] :=
    hmod.of_dvd (Nat.dvd_mul_right q r)
  have hr' : p.1 * r + p.2 * q ≡ p'.1 * r + p'.2 * q [MOD r] :=
    hmod.of_dvd (Nat.dvd_mul_left r q)
  have e1 : (p.1 * r + p.2 * q) % q = (p.1 * r) % q := by
    rw [show p.1 * r + p.2 * q = p.1 * r + q * p.2 from by ring,
      Nat.add_mul_mod_self_left]
  have e2 : (p'.1 * r + p'.2 * q) % q = (p'.1 * r) % q := by
    rw [show p'.1 * r + p'.2 * q = p'.1 * r + q * p'.2 from by ring,
      Nat.add_mul_mod_self_left]
  have e3 : (p.1 * r + p.2 * q) % r = (p.2 * q) % r := by
    rw [show p.1 * r + p.2 * q = p.2 * q + r * p.1 from by ring,
      Nat.add_mul_mod_self_left]
  have e4 : (p'.1 * r + p'.2 * q) % r = (p'.2 * q) % r := by
    rw [show p'.1 * r + p'.2 * q = p'.2 * q + r * p'.1 from by ring,
      Nat.add_mul_mod_self_left]
  have ha1 : p.1 ≡ p'.1 [MOD q] := by
    refine Nat.ModEq.cancel_right_of_coprime hqr ?_
    have hq2 : (p.1 * r) % q = (p'.1 * r) % q := by
      rw [← e1, ← e2]
      exact hq'
    exact hq2
  have ha2 : p.2 ≡ p'.2 [MOD r] := by
    refine Nat.ModEq.cancel_right_of_coprime hqr.symm ?_
    have hr2 : (p.2 * q) % r = (p'.2 * q) % r := by
      rw [← e3, ← e4]
      exact hr'
    exact hr2
  have h1 : p.1 = p'.1 := by
    have h : p.1 % q = p'.1 % q := ha1
    rw [Nat.mod_eq_of_lt hb1, Nat.mod_eq_of_lt hb1'] at h
    exact h
  have h2 : p.2 = p'.2 := by
    have h : p.2 % r = p'.2 % r := ha2
    rw [Nat.mod_eq_of_lt hb2, Nat.mod_eq_of_lt hb2'] at h
    exact h
  exact Prod.ext h1 h2

private lemma card_filter_coprime (n : ℕ) :
    ((Finset.range n).filter (fun a => Nat.Coprime a n)).card = n.totient := by
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext a
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨h.1, Nat.coprime_comm.mp h.2⟩, fun h => ⟨h.1, Nat.coprime_comm.mpr h.2⟩⟩

private lemma crt_residue_bij {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hqr : q.Coprime r) :
    ((Finset.range q).filter (fun a => Nat.Coprime a q) ×ˢ
        (Finset.range r).filter (fun a => Nat.Coprime a r)).image
      (fun p : ℕ × ℕ => (p.1 * r + p.2 * q) % (q * r))
      = (Finset.range (q * r)).filter (fun a => Nat.Coprime a (q * r)) := by
  have hsub : ((Finset.range q).filter (fun a => Nat.Coprime a q) ×ˢ
        (Finset.range r).filter (fun a => Nat.Coprime a r)).image
      (fun p : ℕ × ℕ => (p.1 * r + p.2 * q) % (q * r)) ⊆
      (Finset.range (q * r)).filter (fun a => Nat.Coprime a (q * r)) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact crt_image_mem hq hr hqr hp
  refine Finset.eq_of_subset_of_card_le hsub ?_
  have hinj := crt_injOn hq hr hqr
  rw [Finset.card_image_of_injOn hinj, Finset.card_product, card_filter_coprime,
    card_filter_coprime, card_filter_coprime, Nat.totient_mul hqr]

/-! ### Periodicity in the residue, and multiplicativity of the Ramanujan-type sum -/

private lemma ee_residue_congr (n : ℕ) (hn : 0 < n) {a b : ℕ} (hab : a ≡ b [MOD n])
    (u : ℤ) :
    U1534.ee (((a : ℝ) * (u : ℝ)) / (n : ℝ)) = U1534.ee (((b : ℝ) * (u : ℝ)) / (n : ℝ)) := by
  obtain ⟨k, hk⟩ := Nat.modEq_iff_dvd.mp hab
  -- `hk : (b : ℤ) - (a : ℤ) = (n : ℤ) * k`
  have h2 : (b : ℤ) = (a : ℤ) + (n : ℤ) * k := by
    rw [← hk]; ring
  have hb : (b : ℝ) = (a : ℝ) + (n : ℝ) * (k : ℝ) := by
    have h3 := congrArg (fun z : ℤ => (z : ℝ)) h2
    push_cast at h3
    exact h3
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hn
  have hkey : ((b : ℝ) * (u : ℝ)) / (n : ℝ)
      = ((a : ℝ) * (u : ℝ)) / (n : ℝ) + ((k * u : ℤ) : ℝ) := by
    rw [hb]
    push_cast
    field_simp
    try ring
  rw [hkey, ee_int_add]

private lemma arg_split (q r a1 a2 : ℕ) (hq : 0 < q) (hr : 0 < r) (u : ℤ) :
    ((↑(a1 * r + a2 * q) : ℝ) * (u : ℝ)) / (↑(q * r) : ℝ)
      = (a1 : ℝ) * (u : ℝ) / (q : ℝ) + (a2 : ℝ) * (u : ℝ) / (r : ℝ) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hq
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hr
  push_cast
  field_simp
  try ring

private lemma ram_sum_mul (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (hqr : q.Coprime r) (u : ℤ) :
    (∑ a ∈ (Finset.range (q * r)).filter (fun a => Nat.Coprime a (q * r)),
        U1534.ee (((a : ℝ) * (u : ℝ)) / ((q * r : ℕ) : ℝ)))
      = (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            U1534.ee (((a : ℝ) * (u : ℝ)) / (q : ℝ)))
        * (∑ a ∈ (Finset.range r).filter (fun a => Nat.Coprime a r),
            U1534.ee (((a : ℝ) * (u : ℝ)) / (r : ℝ))) := by
  classical
  set T := (Finset.range q).filter (fun a => Nat.Coprime a q) ×ˢ
    (Finset.range r).filter (fun a => Nat.Coprime a r) with hT
  have hbij := crt_residue_bij hq hr hqr
  have hinj := crt_injOn hq hr hqr
  have hqrpos : 0 < q * r := Nat.mul_pos hq hr
  rw [← hbij, Finset.sum_image hinj]
  trans ∑ p ∈ T, U1534.ee (((↑(p.1 * r + p.2 * q) : ℝ) * (u : ℝ)) / ((q * r : ℕ) : ℝ))
  · refine Finset.sum_congr rfl (fun p _ => ?_)
    refine ee_residue_congr (q * r) hqrpos ?_ u
    show ((p.1 * r + p.2 * q) % (q * r)) % (q * r) = (p.1 * r + p.2 * q) % (q * r)
    rw [Nat.mod_eq_of_lt (Nat.mod_lt _ hqrpos)]
  trans ∑ p ∈ T, U1534.ee (((p.1 : ℝ) * (u : ℝ)) / (q : ℝ))
      * U1534.ee (((p.2 : ℝ) * (u : ℝ)) / (r : ℝ))
  · refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [arg_split q r p.1 p.2 hq hr u, ee_add_real]
  · rw [Finset.sum_product, Finset.sum_mul_sum]

/-- `e(x/q) = e(y/q)` when `q | y - x`. -/
private lemma ee_div_dvd (q : ℕ) (hq : 0 < q) {x y : ℤ} (h : (q : ℤ) ∣ y - x) :
    U1534.ee ((x : ℝ) / (q : ℝ)) = U1534.ee ((y : ℝ) / (q : ℝ)) := by
  obtain ⟨k, hk⟩ := h
  have hy : (y : ℝ) = (x : ℝ) + (q : ℝ) * (k : ℝ) := by
    have h3 := congrArg (fun z : ℤ => (z : ℝ)) hk
    push_cast at h3
    linarith
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hq
  have hkey : (y : ℝ) / (q : ℝ) = (x : ℝ) / (q : ℝ) + (k : ℝ) := by
    rw [hy]
    field_simp
    try ring
  rw [hkey, ee_int_add]

/-- Multiplication by a unit is a bijection of the reduced residues mod `q`. -/
private lemma sum_units_mul {q m : ℕ} (hq : 0 < q) (hm : q.Coprime m) (F : ℕ → ℂ) :
    (∑ b ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), F ((b * m) % q))
      = ∑ b ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), F b := by
  classical
  set U := (Finset.range q).filter (fun a => Nat.Coprime a q) with hU
  have hmaps : ∀ b ∈ U, (b * m) % q ∈ U := by
    intro b hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hq), ?_⟩
    have : (b * m).Coprime q := Nat.Coprime.mul_left hb2 hm.symm
    exact coprime_of_mod this
  have hinj : Set.InjOn (fun b => (b * m) % q) ↑U := by
    intro b hb b' hb' hbb'
    obtain ⟨hb1, -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
    obtain ⟨hb1', -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hb')
    have hb1 : b < q := Finset.mem_range.mp hb1
    have hb1' : b' < q := Finset.mem_range.mp hb1'
    have hme : b * m ≡ b' * m [MOD q] := hbb'
    have h1 : b ≡ b' [MOD q] := Nat.ModEq.cancel_right_of_coprime hm hme
    have h2 : b % q = b' % q := h1
    rw [Nat.mod_eq_of_lt hb1, Nat.mod_eq_of_lt hb1'] at h2
    exact h2
  have hcard : (U.image (fun b => (b * m) % q)).card = U.card := Finset.card_image_of_injOn hinj
  have hsub : U.image (fun b => (b * m) % q) ⊆ U := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    exact hmaps b hb
  have heq : U.image (fun b => (b * m) % q) = U := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [hcard]
  conv_rhs => rw [← heq]
  rw [Finset.sum_image hinj]

/-- `e(a x / q) = e(a y / q)` when `q | y - x`. -/
private lemma ee_mul_div_dvd (q : ℕ) (hq : 0 < q) (a : ℕ) {x y : ℤ}
    (h : (q : ℤ) ∣ y - x) :
    U1534.ee (((a : ℝ) * (x : ℝ)) / (q : ℝ)) = U1534.ee (((a : ℝ) * (y : ℝ)) / (q : ℝ)) := by
  obtain ⟨k, hk⟩ := h
  have hy : (y : ℝ) = (x : ℝ) + (q : ℝ) * (k : ℝ) := by
    have h3 := congrArg (fun z : ℤ => (z : ℝ)) hk
    push_cast at h3
    linarith
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hq
  have hkey : ((a : ℝ) * (y : ℝ)) / (q : ℝ) = ((a : ℝ) * (x : ℝ)) / (q : ℝ) + ((a : ℤ) * k : ℤ) := by
    rw [hy]
    have : ((a : ℤ) * k : ℤ) = (a : ℝ) * (k : ℝ) := by push_cast; ring
    rw [this]
    field_simp
    try ring
  rw [hkey, ee_int_add]

/-- `q` divides the difference of the squares of two congruent naturals. -/
private lemma dvd_sq_sub_sq {q : ℕ} {b b' : ℕ} (h : b ≡ b' [MOD q]) :
    (q : ℤ) ∣ ((b' : ℤ)) ^ 2 - ((b : ℤ)) ^ 2 := by
  obtain ⟨k, hk⟩ := Nat.modEq_iff_dvd.mp h
  refine ⟨k * (((b' : ℤ)) + ((b : ℤ))), ?_⟩
  have hfac : ((b' : ℤ)) ^ 2 - ((b : ℤ)) ^ 2
      = (((b' : ℤ)) - ((b : ℤ))) * (((b' : ℤ)) + ((b : ℤ))) := by ring
  rw [hfac, hk]
  ring

/-- Reindex a reduced residue sum by the Bezout form of CRT. -/
private lemma sum_residue_reindex {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hqr : q.Coprime r)
    (G : ℕ → ℂ) (hper : ∀ a b : ℕ, a ≡ b [MOD q * r] → G a = G b) :
    (∑ a ∈ (Finset.range (q * r)).filter (fun a => Nat.Coprime a (q * r)), G a)
      = ∑ p ∈ ((Finset.range q).filter (fun a => Nat.Coprime a q) ×ˢ
          (Finset.range r).filter (fun a => Nat.Coprime a r)), G (p.1 * r + p.2 * q) := by
  rw [← crt_residue_bij hq hr hqr, Finset.sum_image (crt_injOn hq hr hqr)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  refine hper _ _ ?_
  show ((p.1 * r + p.2 * q) % (q * r)) % (q * r) = (p.1 * r + p.2 * q) % (q * r)
  rw [Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.mul_pos hq hr))]

/-- Periodicity of `e(a u / M)` in the residue `a`. -/
private lemma ee_nat_period (M : ℕ) (hM : 0 < M) {a b : ℕ} (hab : a ≡ b [MOD M]) (u : ℕ) :
    U1534.ee (((a * u : ℕ) : ℝ) / (M : ℝ))
      = U1534.ee (((b * u : ℕ) : ℝ) / (M : ℝ)) := by
  obtain ⟨k, hk⟩ := Nat.modEq_iff_dvd.mp hab
  -- `hk : (b : ℤ) - (a : ℤ) = (M : ℤ) * k`
  have hz : ((b * u : ℕ) : ℤ) = ((a * u : ℕ) : ℤ) + (M : ℤ) * (k * (u : ℤ)) := by
    have h1 : (b : ℤ) = (a : ℤ) + (M : ℤ) * k := by
      rw [← hk]; ring
    calc ((b * u : ℕ) : ℤ) = (b : ℤ) * (u : ℤ) := by push_cast; ring
      _ = ((a : ℤ) + (M : ℤ) * k) * (u : ℤ) := by rw [h1]
      _ = ((a * u : ℕ) : ℤ) + (M : ℤ) * (k * (u : ℤ)) := by push_cast; ring
  have hb : ((b * u : ℕ) : ℝ) = ((a * u : ℕ) : ℝ) + (M : ℝ) * ((k * (u : ℤ) : ℤ) : ℝ) := by
    have h3 := congrArg (fun z : ℤ => (z : ℝ)) hz
    push_cast at h3 ⊢
    linarith
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hM
  have hkey : ((b * u : ℕ) : ℝ) / (M : ℝ)
      = ((a * u : ℕ) : ℝ) / (M : ℝ) + ((k * (u : ℤ) : ℤ) : ℝ) := by
    rw [hb]
    field_simp
    try ring
  rw [hkey, ee_int_add]

/-- Periodicity of `e(- a u / M)` in the residue `a`. -/
private lemma ee_nat_period_neg (M : ℕ) (hM : 0 < M) {a b : ℕ} (hab : a ≡ b [MOD M])
    (u : ℕ) :
    U1534.ee (-(((a * u : ℕ) : ℝ) / (M : ℝ)))
      = U1534.ee (-(((b * u : ℕ) : ℝ) / (M : ℝ))) := by
  obtain ⟨k, hk⟩ := Nat.modEq_iff_dvd.mp hab
  have h1 : (b : ℤ) = (a : ℤ) + (M : ℤ) * k := by
    rw [← hk]; ring
  have hz : ((b * u : ℕ) : ℤ) = ((a * u : ℕ) : ℤ) + (M : ℤ) * (k * (u : ℤ)) := by
    calc ((b * u : ℕ) : ℤ) = (b : ℤ) * (u : ℤ) := by push_cast; ring
      _ = ((a : ℤ) + (M : ℤ) * k) * (u : ℤ) := by rw [h1]
      _ = ((a * u : ℕ) : ℤ) + (M : ℤ) * (k * (u : ℤ)) := by push_cast; ring
  have hb : ((b * u : ℕ) : ℝ) = ((a * u : ℕ) : ℝ) + (M : ℝ) * ((k * (u : ℤ) : ℤ) : ℝ) := by
    have h3 := congrArg (fun z : ℤ => (z : ℝ)) hz
    push_cast at h3 ⊢
    linarith
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hM
  have hkey : (-(((b * u : ℕ) : ℝ) / (M : ℝ)))
      = (-(((a * u : ℕ) : ℝ) / (M : ℝ))) + ((-(k * (u : ℤ) : ℤ) : ℤ) : ℝ) := by
    rw [hb]
    push_cast
    field_simp
    try ring
  rw [hkey, ee_int_add]

/-- Splitting `e((a1 r + a2 q) z ^ 2 / (q r))` into its `q` and `r` parts. -/
private lemma ee_sq_split (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (a1 a2 z : ℕ) :
    U1534.ee (((((a1 * r + a2 * q) * z ^ 2 : ℕ)) : ℝ) / ((q * r : ℕ) : ℝ))
      = U1534.ee (((a1 * z ^ 2 : ℕ) : ℝ) / (q : ℝ))
        * U1534.ee (((a2 * z ^ 2 : ℕ) : ℝ) / (r : ℝ)) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hq
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hr
  have harg : (((((a1 * r + a2 * q) * z ^ 2 : ℕ)) : ℝ) / ((q * r : ℕ) : ℝ))
      = ((a1 * z ^ 2 : ℕ) : ℝ) / (q : ℝ) + ((a2 * z ^ 2 : ℕ) : ℝ) / (r : ℝ) := by
    push_cast
    field_simp
    try ring
  rw [harg, ee_add_real]

/-- The `n`-factor splits the same way. -/
private lemma ee_neg_split (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (a1 a2 n : ℕ) :
    U1534.ee (-((((a1 * r + a2 * q) * n : ℕ) : ℝ) / ((q * r : ℕ) : ℝ)))
      = U1534.ee (-(((a1 * n : ℕ) : ℝ) / (q : ℝ)))
        * U1534.ee (-(((a2 * n : ℕ) : ℝ) / (r : ℝ))) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hq
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hr
  have harg : (-((((a1 * r + a2 * q) * n : ℕ) : ℝ) / ((q * r : ℕ) : ℝ)))
      = (-(((a1 * n : ℕ) : ℝ) / (q : ℝ))) + (-(((a2 * n : ℕ) : ℝ) / (r : ℝ))) := by
    push_cast
    field_simp
    try ring
  rw [harg, ee_add_real]

/-- Periodicity with the multiplier on the left. -/
private lemma ee_nat_period' (M : ℕ) (hM : 0 < M) {a b : ℕ} (hab : a ≡ b [MOD M]) (u : ℕ) :
    U1534.ee (((u * a : ℕ) : ℝ) / (M : ℝ))
      = U1534.ee (((u * b : ℕ) : ℝ) / (M : ℝ)) := by
  rw [mul_comm u a, mul_comm u b]
  exact ee_nat_period M hM hab u

/-- Multiplication by a unit, with the un-reduced product in the index. -/
private lemma sum_units_mul_raw {q m : ℕ} (hq : 0 < q) (hm : q.Coprime m) (F : ℕ → ℂ)
    (hper : ∀ b b' : ℕ, b ≡ b' [MOD q] → F b = F b') :
    (∑ b ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), F (b * m))
      = ∑ b ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), F b := by
  refine (Finset.sum_congr rfl (fun b _ => hper _ _ ?_)).trans (sum_units_mul hq hm F)
  show (b * m) % q = ((b * m) % q) % q
  rw [Nat.mod_eq_of_lt (Nat.mod_lt _ hq)]

/-- The two-variable sum over reduced residues is multiplicative. -/
private lemma inner_mul (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (hqr : q.Coprime r) (n : ℕ) :
    (∑ a ∈ (Finset.range (q * r)).filter (fun a => Nat.Coprime a (q * r)),
        ∑ x ∈ (Finset.range (q * r)).filter (fun x => Nat.Coprime x (q * r)),
          U1534.ee (((a * x ^ 2 : ℕ) : ℝ) / ((q * r : ℕ) : ℝ))
            * U1534.ee (-(((a * n : ℕ) : ℝ) / ((q * r : ℕ) : ℝ))))
      = (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            ∑ x ∈ (Finset.range q).filter (fun x => Nat.Coprime x q),
              U1534.ee (((a * x ^ 2 : ℕ) : ℝ) / (q : ℝ))
                * U1534.ee (-(((a * n : ℕ) : ℝ) / (q : ℝ))))
        * (∑ a ∈ (Finset.range r).filter (fun a => Nat.Coprime a r),
            ∑ x ∈ (Finset.range r).filter (fun x => Nat.Coprime x r),
              U1534.ee (((a * x ^ 2 : ℕ) : ℝ) / (r : ℝ))
                * U1534.ee (-(((a * n : ℕ) : ℝ) / (r : ℝ)))) := by
  classical
  have hM : 0 < q * r := Nat.mul_pos hq hr
  -- (1) reindex the outer variable
  have step1 :
      (∑ a ∈ (Finset.range (q * r)).filter (fun a => Nat.Coprime a (q * r)),
        ∑ x ∈ (Finset.range (q * r)).filter (fun x => Nat.Coprime x (q * r)),
          U1534.ee (((a * x ^ 2 : ℕ) : ℝ) / ((q * r : ℕ) : ℝ))
            * U1534.ee (-(((a * n : ℕ) : ℝ) / ((q * r : ℕ) : ℝ))))
      = ∑ p ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) ×ˢ
            (Finset.range r).filter (fun a => Nat.Coprime a r),
          ∑ x ∈ (Finset.range (q * r)).filter (fun x => Nat.Coprime x (q * r)),
            U1534.ee ((((p.1 * r + p.2 * q) * x ^ 2 : ℕ) : ℝ) / ((q * r : ℕ) : ℝ))
              * U1534.ee (-((((p.1 * r + p.2 * q) * n : ℕ) : ℝ) / ((q * r : ℕ) : ℝ))) := by
    refine sum_residue_reindex hq hr hqr _ ?_
    intro a b hab
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have h1 : U1534.ee (((a * x ^ 2 : ℕ) : ℝ) / ((q * r : ℕ) : ℝ))
        = U1534.ee (((b * x ^ 2 : ℕ) : ℝ) / ((q * r : ℕ) : ℝ)) :=
      ee_nat_period (q * r) hM hab (x ^ 2)
    have h2 : U1534.ee (-(((a * n : ℕ) : ℝ) / ((q * r : ℕ) : ℝ)))
        = U1534.ee (-(((b * n : ℕ) : ℝ) / ((q * r : ℕ) : ℝ))) :=
      ee_nat_period_neg (q * r) hM hab n
    rw [h1, h2]
  rw [step1]
  -- (2) reindex the inner variable
  have step2 : ∀ p ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) ×ˢ
        (Finset.range r).filter (fun a => Nat.Coprime a r),
      (∑ x ∈ (Finset.range (q * r)).filter (fun x => Nat.Coprime x (q * r)),
        U1534.ee ((((p.1 * r + p.2 * q) * x ^ 2 : ℕ) : ℝ) / ((q * r : ℕ) : ℝ))
          * U1534.ee (-((((p.1 * r + p.2 * q) * n : ℕ) : ℝ) / ((q * r : ℕ) : ℝ))))
      = ∑ p' ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) ×ˢ
            (Finset.range r).filter (fun a => Nat.Coprime a r),
          U1534.ee ((((p.1 * r + p.2 * q) * (p'.1 * r + p'.2 * q) ^ 2 : ℕ) : ℝ)
              / ((q * r : ℕ) : ℝ))
            * U1534.ee (-((((p.1 * r + p.2 * q) * n : ℕ) : ℝ) / ((q * r : ℕ) : ℝ))) := by
    intro p _
    refine sum_residue_reindex hq hr hqr _ ?_
    intro x y hxy
    have hsq : x ^ 2 ≡ y ^ 2 [MOD q * r] := by simpa [pow_two] using hxy.mul hxy
    have h1 : U1534.ee ((((p.1 * r + p.2 * q) * x ^ 2 : ℕ) : ℝ) / ((q * r : ℕ) : ℝ))
        = U1534.ee ((((p.1 * r + p.2 * q) * y ^ 2 : ℕ) : ℝ) / ((q * r : ℕ) : ℝ)) :=
      ee_nat_period' (q * r) hM hsq (p.1 * r + p.2 * q)
    rw [h1]
  rw [Finset.sum_congr rfl step2]
  -- (3) split each value into its `q` and `r` parts
  have step3 : ∀ p ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) ×ˢ
        (Finset.range r).filter (fun a => Nat.Coprime a r),
      ∀ p' ∈ (Finset.range q).filter (fun a => Nat.Coprime a q) ×ˢ
        (Finset.range r).filter (fun a => Nat.Coprime a r),
      U1534.ee ((((p.1 * r + p.2 * q) * (p'.1 * r + p'.2 * q) ^ 2 : ℕ) : ℝ)
          / ((q * r : ℕ) : ℝ))
        * U1534.ee (-((((p.1 * r + p.2 * q) * n : ℕ) : ℝ) / ((q * r : ℕ) : ℝ)))
      = (U1534.ee (((p.1 * (p'.1 * r) ^ 2 : ℕ) : ℝ) / (q : ℝ))
            * U1534.ee (-(((p.1 * n : ℕ) : ℝ) / (q : ℝ))))
        * (U1534.ee (((p.2 * (p'.2 * q) ^ 2 : ℕ) : ℝ) / (r : ℝ))
            * U1534.ee (-(((p.2 * n : ℕ) : ℝ) / (r : ℝ)))) := by
    intro p _ p' _
    rw [ee_sq_split q r hq hr p.1 p.2 (p'.1 * r + p'.2 * q),
      ee_neg_split q r hq hr p.1 p.2 n]
    have hmodq : (p'.1 * r + p'.2 * q) ≡ (p'.1 * r) [MOD q] := by
      show (p'.1 * r + p'.2 * q) % q = (p'.1 * r) % q
      rw [show p'.1 * r + p'.2 * q = p'.1 * r + q * p'.2 from by ring,
        Nat.add_mul_mod_self_left]
    have hmodr : (p'.1 * r + p'.2 * q) ≡ (p'.2 * q) [MOD r] := by
      show (p'.1 * r + p'.2 * q) % r = (p'.2 * q) % r
      rw [show p'.1 * r + p'.2 * q = p'.2 * q + r * p'.1 from by ring,
        Nat.add_mul_mod_self_left]
    have hA : U1534.ee (((p.1 * (p'.1 * r + p'.2 * q) ^ 2 : ℕ) : ℝ) / (q : ℝ))
        = U1534.ee (((p.1 * (p'.1 * r) ^ 2 : ℕ) : ℝ) / (q : ℝ)) := by
      simp only [pow_two]
      exact ee_nat_period' q hq (hmodq.mul hmodq) p.1
    have hB : U1534.ee (((p.2 * (p'.1 * r + p'.2 * q) ^ 2 : ℕ) : ℝ) / (r : ℝ))
        = U1534.ee (((p.2 * (p'.2 * q) ^ 2 : ℕ) : ℝ) / (r : ℝ)) := by
      simp only [pow_two]
      exact ee_nat_period' r hr (hmodr.mul hmodr) p.2
    rw [hA, hB]
    ring
  rw [Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun p' hp' => step3 p hp p' hp'))]
  -- (4) remove the multipliers `r` and `q` from the two inner variables
  have subst1 : ∀ a1 a2 x2 : ℕ, (∑ x1 ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        U1534.ee (((a1 * (x1 * r) ^ 2 : ℕ) : ℝ) / (q : ℝ))
          * U1534.ee (-(((a1 * n : ℕ) : ℝ) / (q : ℝ))))
      = ∑ x1 ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
          U1534.ee (((a1 * x1 ^ 2 : ℕ) : ℝ) / (q : ℝ))
            * U1534.ee (-(((a1 * n : ℕ) : ℝ) / (q : ℝ))) := by
    intro a1 a2 x2
    refine sum_units_mul_raw hq hqr (fun b => U1534.ee (((a1 * b ^ 2 : ℕ) : ℝ) / (q : ℝ))
      * U1534.ee (-(((a1 * n : ℕ) : ℝ) / (q : ℝ)))) ?_
    intro b b' hbb
    have hsq : b ^ 2 ≡ b' ^ 2 [MOD q] := by simpa [pow_two] using hbb.mul hbb
    rw [ee_nat_period' q hq hsq a1]
  have subst2 : ∀ a1 a2 x1 : ℕ, (∑ x2 ∈ (Finset.range r).filter (fun a => Nat.Coprime a r),
        U1534.ee (((a2 * (x2 * q) ^ 2 : ℕ) : ℝ) / (r : ℝ))
          * U1534.ee (-(((a2 * n : ℕ) : ℝ) / (r : ℝ))))
      = ∑ x2 ∈ (Finset.range r).filter (fun a => Nat.Coprime a r),
          U1534.ee (((a2 * x2 ^ 2 : ℕ) : ℝ) / (r : ℝ))
            * U1534.ee (-(((a2 * n : ℕ) : ℝ) / (r : ℝ))) := by
    intro a1 a2 x1
    refine sum_units_mul_raw hr hqr.symm (fun b => U1534.ee (((a2 * b ^ 2 : ℕ) : ℝ) / (r : ℝ))
      * U1534.ee (-(((a2 * n : ℕ) : ℝ) / (r : ℝ)))) ?_
    intro b b' hbb
    have hsq : b ^ 2 ≡ b' ^ 2 [MOD r] := by simpa [pow_two] using hbb.mul hbb
    rw [ee_nat_period' r hr hsq a2]
  simp only [Finset.sum_product]
  trans ∑ a1 ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∑ a2 ∈ (Finset.range r).filter (fun a => Nat.Coprime a r), ∑ x1 ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (U1534.ee (((a1 * (x1 * r) ^ 2 : ℕ) : ℝ) / (q : ℝ)) * U1534.ee (-(((a1 * n : ℕ) : ℝ) / (q : ℝ)))) * (∑ x2 ∈ (Finset.range r).filter (fun a => Nat.Coprime a r), U1534.ee (((a2 * (x2 * q) ^ 2 : ℕ) : ℝ) / (r : ℝ)) * U1534.ee (-(((a2 * n : ℕ) : ℝ) / (r : ℝ))))
  · refine Finset.sum_congr rfl (fun a1 _ => Finset.sum_congr rfl (fun a2 _ =>
      Finset.sum_congr rfl (fun x1 _ => ?_)))
    rw [← Finset.mul_sum, subst2 a1 a2 x1]
  trans ∑ a1 ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∑ a2 ∈ (Finset.range r).filter (fun a => Nat.Coprime a r), (∑ x1 ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), U1534.ee (((a1 * (x1 * r) ^ 2 : ℕ) : ℝ) / (q : ℝ)) * U1534.ee (-(((a1 * n : ℕ) : ℝ) / (q : ℝ)))) * (∑ x2 ∈ (Finset.range r).filter (fun a => Nat.Coprime a r), U1534.ee (((a2 * (x2 * q) ^ 2 : ℕ) : ℝ) / (r : ℝ)) * U1534.ee (-(((a2 * n : ℕ) : ℝ) / (r : ℝ))))
  · refine Finset.sum_congr rfl (fun a1 _ => Finset.sum_congr rfl (fun a2 _ => ?_))
    rw [Finset.sum_mul]
  trans ∑ a1 ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ∑ a2 ∈ (Finset.range r).filter (fun a => Nat.Coprime a r), (∑ x1 ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), U1534.ee (((a1 * x1 ^ 2 : ℕ) : ℝ) / (q : ℝ)) * U1534.ee (-(((a1 * n : ℕ) : ℝ) / (q : ℝ)))) * (∑ x2 ∈ (Finset.range r).filter (fun a => Nat.Coprime a r), U1534.ee (((a2 * x2 ^ 2 : ℕ) : ℝ) / (r : ℝ)) * U1534.ee (-(((a2 * n : ℕ) : ℝ) / (r : ℝ))))
  · refine Finset.sum_congr rfl (fun a1 _ => Finset.sum_congr rfl (fun a2 _ => ?_))
    rw [subst1 a1 a2 0, subst2 a1 a2 0]
  trans ∑ a1 ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), (∑ x1 ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), U1534.ee (((a1 * x1 ^ 2 : ℕ) : ℝ) / (q : ℝ)) * U1534.ee (-(((a1 * n : ℕ) : ℝ) / (q : ℝ)))) * (∑ a2 ∈ (Finset.range r).filter (fun a => Nat.Coprime a r), ∑ x2 ∈ (Finset.range r).filter (fun a => Nat.Coprime a r), U1534.ee (((a2 * x2 ^ 2 : ℕ) : ℝ) / (r : ℝ)) * U1534.ee (-(((a2 * n : ℕ) : ℝ) / (r : ℝ))))
  · refine Finset.sum_congr rfl (fun a1 _ => ?_)
    rw [Finset.mul_sum]
  · rw [← Finset.sum_mul]


/-- `A2 n q` as a two-variable sum over reduced residues. -/
private lemma A2_eq_double (n q : ℕ) :
    U1534.A2 n q
      = ((ArithmeticFunction.moebius q : ℤ) : ℂ) / ((Nat.totient q : ℂ) ^ 2)
        * ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
            ∑ x ∈ (Finset.range q).filter (fun x => Nat.Coprime x q),
              U1534.ee (((a * x ^ 2 : ℕ) : ℝ) / (q : ℝ))
                * U1534.ee (-(((a * n : ℕ) : ℝ) / (q : ℝ))) := by
  unfold U1534.A2 U1534.gaussS
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [neg_div]

/-- `A2 n .` is multiplicative in the modulus. -/
private lemma A2_mul_coprime {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (hqr : q.Coprime r)
    (n : ℕ) : U1534.A2 n (q * r) = U1534.A2 n q * U1534.A2 n r := by
  rw [A2_eq_double n (q * r), A2_eq_double n q, A2_eq_double n r,
    inner_mul q r hq hr hqr n]
  have hμ : ((ArithmeticFunction.moebius (q * r) : ℤ) : ℂ)
      = ((ArithmeticFunction.moebius q : ℤ) : ℂ) * ((ArithmeticFunction.moebius r : ℤ) : ℂ) := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hqr]
    push_cast
    ring
  have hφ : ((Nat.totient (q * r) : ℂ))
      = (Nat.totient q : ℂ) * (Nat.totient r : ℂ) := by
    rw [Nat.totient_mul hqr]
    push_cast
    ring
  have hqφ : (Nat.totient q : ℂ) ≠ 0 := by
    have h : 0 < Nat.totient q := Nat.totient_pos.mpr hq
    exact_mod_cast h.ne'
  have hrφ : (Nat.totient r : ℂ) ≠ 0 := by
    have h : 0 < Nat.totient r := Nat.totient_pos.mpr hr
    exact_mod_cast h.ne'
  rw [hμ, hφ]
  field_simp
  try ring


/-
DONE in this file (all compile, no sorry): the leaf is reduced to one analytic bound.

  ee_add_real, ee_int_add                        e(x+y) = e(x)e(y), periodicity of e
  crt_coprime, coprime_of_mod, crt_image_mem, crt_injOn, card_filter_coprime,
  crt_residue_bij                                Bezout-form CRT bijection on reduced residues
  ee_residue_congr, ee_nat_period, ee_nat_period', ee_nat_period_neg, ee_div_dvd,
  ee_mul_div_dvd, dvd_sq_sub_sq                  periodicity in the residue
  arg_split, ee_sq_split, ee_neg_split           splitting e((a1 r + a2 q) z^2 / (q r))
  sum_residue_reindex                            one reduced residue sum, reindexed by CRT
  sum_units_mul, sum_units_mul_raw               multiplication by a unit is a bijection
  ram_sum_mul                                    sum of e(a u / (q r)) factorises
  inner_mul                                      the two-variable sum is multiplicative
  A2_eq_double, A2_one                           A2 as a two-variable reduced-residue sum
  A2_mul_coprime                                 A2 n (q*r) = A2 n q * A2 n r (coprime q r)
  A2_prod_primes                                 A2 n (prod of primes) = prod of A2 n p
  prod_expansion, product2_eq_subsets            prod (1 + A2 n p) = sum over subsets
  squarefree_prod_primes, sum_squarefree_eq_subsets, sum_smooth_eq_subsets
                                                 squarefree / smooth q <= m <-> subsets
  mem_primes_iff, smoothWeight_eq_indicator, sum_smoothWeight_eq, smooth_sum_Icc
                                                 Psi-weighted sums as subset sums
  series_tail_eq                                 series2 - tail2 = subset sum below max
  rem_eq_subset_tail                             THE REDUCTION:
      series2 n P - product2 n Q - tail2 n P Q0 Q
        = - sum over t in s.powerset with max(floor P)(floor Q0) < t.prod id of A2 n (t.prod id)
  prod_le_prod_real, A2_norm_le                  |A2 n (t.prod)| <= prod over p in t of (p+6)/p^2

REMAINING, in order:

 1. `prime_pow_sum_le` (DONE-DOWN-TO-THIS): with `sigma = 1/(2 log z)`, `z = floor Q + 1`,
      sum over primes p <= z of p^(sigma-1) <= C (1 + log log z).
    CORRECTION to an earlier note in this file: an estimate of this strength IS needed
    (it is Mertens' first theorem in weak form, absent from Mathlib and the repo). It is
    however elementary and reachable from what Mathlib has, via the dyadic block argument
    and nothing else:
      for p in (2^(k-1), 2^k] one has p^(sigma-1) <= 2^((k-1)(sigma-1)) and
        #{p in that block} <= theta(2^k) / ((k-1) log 2),   theta the Chebyshev function,
      and `Chebyshev.theta_le_log4_mul_x` gives theta(2^k) <= log 4 * 2^k, so the block mass
      is <= (log 4 / log 2) * 2^(1-sigma) * 2^(k sigma)/(k-1) <= C/(k-1) because
      2^(k sigma) <= z^sigma = exp(1/2). Summing over k <= log_2 z gives C (1 + log log z).
    So this needs: `Nat.primesLE` (Mathlib), `Chebyshev.theta_eq_sum_primesLE_log`,
    `Chebyshev.theta_le_log4_mul_x`, the dyadic partition of `primesLE z`, and
    `sum_{k<=K} 1/k <= 1 + log K`. No new import, no PNT, no Abel summation.
 2. `subset_tail_le_log`: combining `subset_tail_rankin`, `euler_product_le` and (1),
      sum over t with Q0 < t.prod of prod (p+6)/p^2 <= Q0^(-sigma) * C' (1 + log log z)^(7e^...)
      <= C_A (log x)^(-A) for every A, since with Q0 = floor (y^(1/3)), x^eps <= y <= x,
        log Q0 / (2 log Q) >= (eps/6)(log x)^eps
      and an exponential in a positive power of log x beats any power of log x.
 3. Glue to the leaf: `A2_norm_le` + (2) give
      ‖series2 n P - product2 n Q - tail2 n P Q0 Q‖ <= sum over t with Q0 < t.prod of ‖A2 n (prod t)‖
      <= C_A (log x)^(-A),  hence the leaf's `C / (log x)^A` after squaring.
    (`rem_eq_subset_tail` supplies the exact identity; the `max` cutoff is >= floor Q0, so
    the sum with cutoff `max` is at most the sum with cutoff `Q0`.)
-/

/-- `A2 n 1 = 1`. -/
private lemma A2_one (n : ℕ) : U1534.A2 n 1 = 1 := by
  unfold U1534.A2 U1534.gaussS
  have h1 : (Finset.range 1).filter (fun a => Nat.Coprime a 1) = {0} := by decide
  rw [h1, ArithmeticFunction.moebius_apply_one, Nat.totient_one]
  simp [U1534.ee, Complex.exp_zero]

/-- `A2 n .` is multiplicative over a set of distinct primes. -/
private lemma A2_prod_primes (n : ℕ) :
    ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → U1534.A2 n (s.prod id) = ∏ p ∈ s, U1534.A2 n p := by
  intro s
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.prod_empty]
    simpa using A2_one n
  · intro a s ha hih hprime
    have hpa : a.Prime := hprime a (Finset.mem_insert_self a s)
    have hs : ∀ p ∈ s, p.Prime := fun p hp => hprime p (Finset.mem_insert_of_mem hp)
    have hcop : a.Coprime (s.prod id) := by
      refine Nat.Coprime.prod_right (fun p hp => ?_)
      exact (Nat.coprime_primes hpa (hs p hp)).mpr (by rintro rfl; exact ha hp)
    have hpos : 0 < s.prod id :=
      Finset.prod_pos (fun p hp => (hs p hp).pos)
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    show U1534.A2 n (a * s.prod id) = U1534.A2 n a * s.prod (fun p => U1534.A2 n p)
    rw [A2_mul_coprime hpa.pos hpos hcop n, hih hs]


/-- Expanding an Euler product into a sum over squarefree divisors, written as
subsets of the prime set. -/
private lemma prod_expansion (n : ℕ) (s : Finset ℕ) (hprime : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, (1 + U1534.A2 n p) = ∑ t ∈ s.powerset, U1534.A2 n (t.prod id) := by
  classical
  rw [Finset.prod_add]
  trans ∑ t ∈ s.powerset, ∏ i ∈ s \ t, U1534.A2 n i
  · refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.prod_const_one, one_mul]
  trans ∑ t ∈ s.powerset, U1534.A2 n ((s \ t).prod id)
  · refine Finset.sum_congr rfl (fun t _ => ?_)
    refine (A2_prod_primes n (s \ t) (fun p hp => hprime p (Finset.mem_sdiff.mp hp).1)).symm
  · refine Finset.sum_bij (fun t _ => s \ t) (fun t _ => Finset.mem_powerset.mpr Finset.sdiff_subset)
      ?_ ?_ ?_
    · intro t ht t' ht' heq
      have ht : t ⊆ s := Finset.mem_powerset.mp ht
      have ht' : t' ⊆ s := Finset.mem_powerset.mp ht'
      have h := heq
      rw [← Finset.sdiff_sdiff_eq_self ht, ← Finset.sdiff_sdiff_eq_self ht', h]
    · intro b hb
      refine ⟨s \ b, Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
      exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hb)
    · intro t _
      rfl


/-- A product of distinct primes is squarefree. -/
private lemma squarefree_prod_primes (t : Finset ℕ) (h : ∀ p ∈ t, p.Prime) :
    Squarefree (t.prod id) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using squarefree_one (R := ℕ)
  | insert a t ha ih =>
    have hpa : a.Prime := h a (Finset.mem_insert_self a t)
    have ht : ∀ p ∈ t, p.Prime := fun p hp => h p (Finset.mem_insert_of_mem hp)
    have hcop : a.Coprime (t.prod id) := by
      refine Nat.Coprime.prod_right (fun p hp => ?_)
      exact (Nat.coprime_primes hpa (ht p hp)).mpr (by rintro rfl; exact ha hp)
    have hins : (insert a t).prod id = a * t.prod id := by
      rw [Finset.prod_insert ha]; rfl
    rw [hins]
    exact (Nat.squarefree_mul hcop).mpr ⟨hpa.squarefree, ih ht⟩

/-- Squarefree integers up to `Q0` correspond to subsets of the primes up to `Q0`
with product at most `Q0`. -/
private lemma sum_squarefree_eq_subsets (n : ℕ) (s : Finset ℕ) (hprime : ∀ p ∈ s, p.Prime)
    (hcover : ∀ p : ℕ, p.Prime → p ∈ s) (Q0 : ℕ) :
    (∑ q ∈ (Finset.Icc 1 Q0).filter (fun q => Squarefree q), U1534.A2 n q)
      = ∑ t ∈ s.powerset.filter (fun t => t.prod id ≤ Q0), U1534.A2 n (t.prod id) := by
  classical
  refine (Finset.sum_bij (s := s.powerset.filter (fun t => t.prod id ≤ Q0))
    (t := (Finset.Icc 1 Q0).filter (fun q => Squarefree q))
    (f := fun t => U1534.A2 n (t.prod id)) (g := fun q => U1534.A2 n q)
    (fun t _ => t.prod id) ?_ ?_ ?_ ?_).symm
  · intro t ht
    obtain ⟨hts, hle⟩ := Finset.mem_filter.mp ht
    have hsub : t ⊆ s := Finset.mem_powerset.mp hts
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, hle⟩, ?_⟩
    · exact Finset.one_le_prod (fun p hp => (hprime p (hsub hp)).one_le)
    · exact squarefree_prod_primes t (fun p hp => hprime p (hsub hp))
  · intro t ht t' ht' heq
    have hsub : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
    have hsub' : t' ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht').1
    have h1 : (∏ p ∈ t, p).primeFactors = t :=
      Nat.primeFactors_prod (fun p hp => hprime p (hsub hp))
    have h2 : (∏ p ∈ t', p).primeFactors = t' :=
      Nat.primeFactors_prod (fun p hp => hprime p (hsub' hp))
    have heq' : (∏ p ∈ t, p) = (∏ p ∈ t', p) := heq
    calc t = (∏ p ∈ t, p).primeFactors := h1.symm
      _ = (∏ p ∈ t', p).primeFactors := by rw [heq']
      _ = t' := h2
  · intro q hq
    obtain ⟨hIcc, hsq⟩ := Finset.mem_filter.mp hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hIcc).1
    have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq1
    have hle : q ≤ Q0 := (Finset.mem_Icc.mp hIcc).2
    refine ⟨q.primeFactors, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
      · intro p hp
        obtain ⟨hpp, -, -⟩ := Nat.mem_primeFactors.mp hp
        exact hcover p hpp
      · have hpf : q.primeFactors.prod id = q := Nat.prod_primeFactors_of_squarefree hsq
        rw [hpf]
        exact hle
    · exact Nat.prod_primeFactors_of_squarefree hsq
  · intro t _; rfl


/-- Smooth squarefree integers up to `m` correspond to subsets of the primes in `s`
with product at most `m`. -/
private lemma sum_smooth_eq_subsets (n : ℕ) (s : Finset ℕ) (hprime : ∀ p ∈ s, p.Prime)
    (m : ℕ) :
    (∑ q ∈ (Finset.Icc 1 m).filter
        (fun q => (∀ p, p.Prime → p ∣ q → p ∈ s) ∧ Squarefree q), U1534.A2 n q)
      = ∑ t ∈ s.powerset.filter (fun t => t.prod id ≤ m), U1534.A2 n (t.prod id) := by
  classical
  refine (Finset.sum_bij (s := s.powerset.filter (fun t => t.prod id ≤ m))
    (t := (Finset.Icc 1 m).filter
      (fun q => (∀ p, p.Prime → p ∣ q → p ∈ s) ∧ Squarefree q))
    (f := fun t => U1534.A2 n (t.prod id)) (g := fun q => U1534.A2 n q)
    (fun t _ => t.prod id) ?_ ?_ ?_ ?_).symm
  · intro t ht
    obtain ⟨hts, hle⟩ := Finset.mem_filter.mp ht
    have hsub : t ⊆ s := Finset.mem_powerset.mp hts
    have hpr : ∀ p ∈ t, p.Prime := fun p hp => hprime p (hsub hp)
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, hle⟩, ?_, ?_⟩
    · exact Finset.one_le_prod (fun p hp => (hpr p hp).one_le)
    · intro p hpp hpdvd
      have hmem : p ∈ t := by
        obtain ⟨a, hat, hdvd⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hpp) (fun x => x)).mp hpdvd
        have hap : Nat.Prime a := hpr a hat
        rcases (Nat.dvd_prime hap).mp hdvd with h1 | h2
        · exact absurd h1 hpp.ne_one
        · rw [h2]
          exact hat
      exact hsub hmem
    · exact squarefree_prod_primes t hpr
  · intro t ht t' ht' heq
    have hsub : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
    have hsub' : t' ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht').1
    have h1 : (∏ p ∈ t, p).primeFactors = t :=
      Nat.primeFactors_prod (fun p hp => hprime p (hsub hp))
    have h2 : (∏ p ∈ t', p).primeFactors = t' :=
      Nat.primeFactors_prod (fun p hp => hprime p (hsub' hp))
    have heq' : (∏ p ∈ t, p) = (∏ p ∈ t', p) := heq
    calc t = (∏ p ∈ t, p).primeFactors := h1.symm
      _ = (∏ p ∈ t', p).primeFactors := by rw [heq']
      _ = t' := h2
  · intro q hq
    obtain ⟨hIcc, hsmooth, hsq⟩ := Finset.mem_filter.mp hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hIcc).1
    have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq1
    have hle : q ≤ m := (Finset.mem_Icc.mp hIcc).2
    refine ⟨q.primeFactors, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
      · intro p hp
        obtain ⟨hpp, hpdvd, -⟩ := Nat.mem_primeFactors.mp hp
        exact hsmooth p hpp hpdvd
      · have hpf : q.primeFactors.prod id = q := Nat.prod_primeFactors_of_squarefree hsq
        rw [hpf]
        exact hle
    · exact Nat.prod_primeFactors_of_squarefree hsq
  · intro t _; rfl


/-- A prime lies in the prime set cut off at `Q` exactly when it is at most `Q`. -/
private lemma mem_primes_iff (Q : ℝ) (hQ : 0 ≤ Q) {p : ℕ} (hp : p.Prime) :
    (p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime ↔ (p : ℝ) ≤ Q) := by
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hlt, -⟩
    have h1 : p ≤ ⌊Q⌋₊ := Nat.lt_succ_iff.mp hlt
    exact le_trans (by exact_mod_cast h1) (Nat.floor_le hQ)
  · intro hle
    refine ⟨?_, hp⟩
    have h1 : p ≤ ⌊Q⌋₊ := Nat.le_floor hle
    omega

/-- The smooth weight is the indicator of the integers all of whose prime factors
lie in the prime set cut off at `Q`. -/
private lemma smoothWeight_eq_indicator (Q : ℝ) (hQ : 0 ≤ Q) (q : ℕ) :
    (Task129b.smoothWeight q Q : ℂ)
      = if (∀ p, p.Prime → p ∣ q → p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime)
          then 1 else 0 := by
  unfold LeanLab.KumchevLiu2007.Task129b.smoothWeight
  by_cases h : ∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) ≤ Q
  · have h' : ∀ p, p.Prime → p ∣ q →
        p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime :=
      fun p hp hpq => (mem_primes_iff Q hQ hp).mpr (h p hp hpq)
    simp only [if_pos h, if_pos h']
    norm_num
  · have h' : ¬ ∀ p, p.Prime → p ∣ q →
        p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime := by
      intro hc
      exact h fun p hp hpq => (mem_primes_iff Q hQ hp).mp (hc p hp hpq)
    simp only [if_neg h, if_neg h']
    norm_num

/-- The `Psi`-weighted sum over a range of integers is a sum over its smooth
squarefree parts. -/
private lemma sum_smoothWeight_eq (n : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) (m : ℕ) :
    (∑ q ∈ Finset.Icc 1 m, (Task129b.smoothWeight q Q : ℂ) * U1534.A2 n q)
      = ∑ q ∈ (Finset.Icc 1 m).filter
          (fun q => (∀ p, p.Prime → p ∣ q →
              p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime) ∧ Squarefree q),
          U1534.A2 n q := by
  classical
  have hstep : ∀ q ∈ Finset.Icc 1 m,
      (Task129b.smoothWeight q Q : ℂ) * U1534.A2 n q
        = if (∀ p, p.Prime → p ∣ q →
              p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime) then U1534.A2 n q else 0 := by
    intro q _
    rw [smoothWeight_eq_indicator Q hQ q]
    by_cases h : ∀ p, p.Prime → p ∣ q → p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime
    · simp only [if_pos h, one_mul]
    · simp only [if_neg h, zero_mul]
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter]
  have hsub : (Finset.Icc 1 m).filter
        (fun q => (∀ p, p.Prime → p ∣ q →
            p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime) ∧ Squarefree q)
      ⊆ (Finset.Icc 1 m).filter (fun q => ∀ p, p.Prime → p ∣ q →
          p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime) := by
    intro q hq
    obtain ⟨h1, h2, -⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨h1, h2⟩
  refine (Finset.sum_subset hsub ?_).symm
  intro q hq hqnot
  refine LeanLab.KumchevLiu2007.Task129b.A2_eq_zero_of_not_squarefree n q ?_
  intro hsq
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hq
  exact hqnot (Finset.mem_filter.mpr ⟨h1, h2, hsq⟩)


/-- The `Psi`-weighted sum over `[1, m]` equals the subset sum with product at most `m`. -/
private lemma smooth_sum_Icc (n : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) (m : ℕ) :
    (∑ q ∈ Finset.Icc 1 m, (LeanLab.KumchevLiu2007.Task129b.smoothWeight q Q : ℂ) * U1534.A2 n q)
      = ∑ t ∈ ((Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime).powerset.filter
          (fun t => t.prod id ≤ m), U1534.A2 n (t.prod id) := by
  refine (sum_smoothWeight_eq n Q hQ m).trans (sum_smooth_eq_subsets n _ ?_ m)
  intro p hp
  exact (Finset.mem_filter.mp hp).2

/-- `series2 - tail2` is the subset sum below the larger of the two cutoffs. -/
private lemma series_tail_eq (n : ℕ) (P Q Q0 : ℝ) (hQ : 0 ≤ Q) (hP : 0 < P) (hPQ : P ≤ Q) :
    LeanLab.KumchevLiu2007.Task129.series2 n P
        - LeanLab.KumchevLiu2007.Task129b.tail2 n P Q0 Q
      = ∑ t ∈ ((Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime).powerset.filter
          (fun t => t.prod id ≤ max ⌊P⌋₊ ⌊Q0⌋₊), U1534.A2 n (t.prod id) := by
  classical
  have hPQ' : ⌊P⌋₊ ≤ ⌊Q⌋₊ := Nat.floor_mono hPQ
  have hser : LeanLab.KumchevLiu2007.Task129.series2 n P
      = ∑ q ∈ Finset.Icc 1 ⌊P⌋₊,
          (LeanLab.KumchevLiu2007.Task129b.smoothWeight q Q : ℂ) * U1534.A2 n q := by
    unfold LeanLab.KumchevLiu2007.Task129.series2
    refine Finset.sum_congr rfl (fun q hq => ?_)
    obtain ⟨hq1, hqP⟩ := Finset.mem_Icc.mp hq
    have hqQ : q ≤ ⌊Q⌋₊ := le_trans hqP hPQ'
    have hsmooth : ∀ p, p.Prime → p ∣ q →
        p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime := by
      intro p hp hpq
      have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq1
      have hpq' : p ≤ q := Nat.le_of_dvd hqpos hpq
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩
    rw [smoothWeight_eq_indicator Q hQ q, if_pos hsmooth]
    ring
  have htail : LeanLab.KumchevLiu2007.Task129b.tail2 n P Q0 Q
      = -∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊Q0⌋₊,
          (LeanLab.KumchevLiu2007.Task129b.smoothWeight q Q : ℂ) * U1534.A2 n q := by
    unfold LeanLab.KumchevLiu2007.Task129b.tail2
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  rw [hser, htail]
  by_cases hle : ⌊P⌋₊ ≤ ⌊Q0⌋₊
  · rw [max_eq_right hle, sub_neg_eq_add]
    have hsplit : (∑ q ∈ Finset.Icc 1 ⌊P⌋₊,
          (LeanLab.KumchevLiu2007.Task129b.smoothWeight q Q : ℂ) * U1534.A2 n q)
        + (∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊Q0⌋₊,
          (LeanLab.KumchevLiu2007.Task129b.smoothWeight q Q : ℂ) * U1534.A2 n q)
        = ∑ q ∈ Finset.Icc 1 ⌊Q0⌋₊,
          (LeanLab.KumchevLiu2007.Task129b.smoothWeight q Q : ℂ) * U1534.A2 n q := by
      have h1 := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 ⌊Q0⌋₊)
        (fun q : ℕ => q ≤ ⌊P⌋₊)
        (fun q => (LeanLab.KumchevLiu2007.Task129b.smoothWeight q Q : ℂ) * U1534.A2 n q)
      rw [← h1]
      congr 1
      · refine Finset.sum_congr ?_ (fun q _ => rfl)
        ext q
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      · refine Finset.sum_congr ?_ (fun q _ => rfl)
        ext q
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
        omega
    rw [hsplit, smooth_sum_Icc n Q hQ ⌊Q0⌋₊]
  · have hPle : ⌊Q0⌋₊ ≤ ⌊P⌋₊ := le_of_lt (not_le.mp hle)
    rw [max_eq_left hPle]
    have hzero : (∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊Q0⌋₊,
        (LeanLab.KumchevLiu2007.Task129b.smoothWeight q Q : ℂ) * U1534.A2 n q) = 0 := by
      refine Finset.sum_eq_zero (fun q hq => ?_)
      obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hq
      omega
    rw [hzero, neg_zero, sub_zero, smooth_sum_Icc n Q hQ ⌊P⌋₊]


/-- `product2` as the subset sum of `A2` over the prime factors up to `Q`. -/
private lemma product2_eq_subsets (n : ℕ) (Q : ℝ) :
    LeanLab.KumchevLiu2007.Task129b.product2 n Q
      = ∑ t ∈ ((Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime).powerset,
          U1534.A2 n (t.prod id) := by
  unfold LeanLab.KumchevLiu2007.Task129b.product2
  exact prod_expansion n _ (fun p hp => (Finset.mem_filter.mp hp).2)

/-- The exact form of the truncation error: minus the `A2` mass of the subsets whose
product exceeds both cutoffs. -/
private lemma rem_eq_subset_tail (n : ℕ) (P Q Q0 : ℝ) (hQ : 0 ≤ Q) (hP : 0 < P)
    (hPQ : P ≤ Q) :
    LeanLab.KumchevLiu2007.Task129.series2 n P
        - LeanLab.KumchevLiu2007.Task129b.product2 n Q
        - LeanLab.KumchevLiu2007.Task129b.tail2 n P Q0 Q
      = -∑ t ∈ ((Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime).powerset.filter
          (fun t => max ⌊P⌋₊ ⌊Q0⌋₊ < t.prod id), U1534.A2 n (t.prod id) := by
  classical
  have hstep : LeanLab.KumchevLiu2007.Task129.series2 n P
        - LeanLab.KumchevLiu2007.Task129b.product2 n Q
        - LeanLab.KumchevLiu2007.Task129b.tail2 n P Q0 Q
      = (LeanLab.KumchevLiu2007.Task129.series2 n P
          - LeanLab.KumchevLiu2007.Task129b.tail2 n P Q0 Q)
        - LeanLab.KumchevLiu2007.Task129b.product2 n Q := by ring
  rw [hstep, series_tail_eq n P Q Q0 hQ hP hPQ, product2_eq_subsets n Q]
  have h2 := Finset.sum_filter_add_sum_filter_not
    (((Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime).powerset)
    (fun t : Finset ℕ => t.prod id ≤ max ⌊P⌋₊ ⌊Q0⌋₊)
    (fun t => U1534.A2 n (t.prod id))
  rw [← h2]
  have hcongr : ((((Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime).powerset).filter
        (fun t : Finset ℕ => ¬ t.prod id ≤ max ⌊P⌋₊ ⌊Q0⌋₊))
      = ((((Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime).powerset).filter
        (fun t : Finset ℕ => max ⌊P⌋₊ ⌊Q0⌋₊ < t.prod id)) := by
    exact Finset.filter_congr (fun t _ => not_le)
  rw [hcongr]
  ring


/-- Monotonicity of a finite product of nonnegative reals (no `MulLeftMono` for `ℝ`
in this build, so by induction). -/
private lemma prod_le_prod_real {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hfs : 0 ≤ ∏ i ∈ s, f i :=
      Finset.prod_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have h1 : f a ≤ g a := h a (Finset.mem_insert_self a s)
    have h2 : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact mul_le_mul h1 h2 hfs (le_trans hfa h1)

/-- Size bound for `A2` on a product of distinct primes. -/
private lemma A2_norm_le (n : ℕ) (t : Finset ℕ) (hprime : ∀ p ∈ t, p.Prime) :
    ‖U1534.A2 n (t.prod id)‖ ≤ ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2 := by
  classical
  rw [A2_prod_primes n t hprime, Complex.norm_prod]
  refine prod_le_prod_real t (fun p => ‖U1534.A2 n p‖)
    (fun p => ((p : ℝ) + 6) / (p : ℝ) ^ 2) (fun p _ => norm_nonneg _) (fun p hp => ?_)
  haveI : Fact p.Prime := ⟨hprime p hp⟩
  refine (LeanLab.KumchevLiu2007.Task129b.A2_prime_norm_le_inv_add p n).trans ?_
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hkey : (1 : ℝ) / (p : ℝ) + 6 / (p : ℝ) ^ 2 = ((p : ℝ) + 6) / (p : ℝ) ^ 2 := by
    field_simp
  rw [hkey]


/-- Expanding a product of `(1 + g p)` into a sum over subsets (generic in the target
semiring, so it serves both the complex and the real case). -/
private lemma prod_add_expansion {M : Type*} [CommSemiring M] (s : Finset ℕ) (g : ℕ → M) :
    ∏ p ∈ s, (1 + g p) = ∑ t ∈ s.powerset, ∏ p ∈ t, g p := by
  classical
  rw [Finset.prod_add]
  trans ∑ t ∈ s.powerset, ∏ i ∈ s \ t, g i
  · refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.prod_const_one, one_mul]
  · refine Finset.sum_bij (fun t _ => s \ t) (fun t _ => Finset.mem_powerset.mpr Finset.sdiff_subset)
      ?_ ?_ ?_
    · intro t ht t' ht' heq
      have ht : t ⊆ s := Finset.mem_powerset.mp ht
      have ht' : t' ⊆ s := Finset.mem_powerset.mp ht'
      have h := heq
      rw [← Finset.sdiff_sdiff_eq_self ht, ← Finset.sdiff_sdiff_eq_self ht', h]
    · intro b hb
      refine ⟨s \ b, Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
      exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hb)
    · intro t _
      rfl

/-- Rankin's shift applied to the subset tail: the `A2` mass above `Q0` costs a factor
`Q0 ^ (-sigma)` and an Euler product. -/
private lemma subset_tail_rankin (s : Finset ℕ) (hprime : ∀ p ∈ s, p.Prime)
    (Q0 : ℝ) (hQ0 : 0 < Q0) (σ : ℝ) (hσ : 0 < σ) :
    (∑ t ∈ s.powerset.filter (fun t => Q0 < ((t.prod id : ℕ) : ℝ)),
        ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2)
      ≤ Q0 ^ (-σ) * ∏ p ∈ s,
          (1 + (p : ℝ) ^ σ * (((p : ℝ) + 6) / (p : ℝ) ^ 2)) := by
  classical
  have hw : ∀ p ∈ s, (0 : ℝ) ≤ ((p : ℝ) + 6) / (p : ℝ) ^ 2 := by
    intro p _
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p ‹p ∈ s›).two_le
    positivity
  -- pointwise Rankin bound on the filtered set
  have hpt : ∀ t ∈ s.powerset.filter (fun t => Q0 < ((t.prod id : ℕ) : ℝ)),
      ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2
        ≤ Q0 ^ (-σ) * ((((t.prod id : ℕ)) : ℝ) ^ σ)
            * ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2 := by
    intro t ht
    obtain ⟨-, hgt⟩ := Finset.mem_filter.mp ht
    have hX : (0 : ℝ) ≤ (((t.prod id : ℕ)) : ℝ) := by positivity
    have hge : (1 : ℝ) ≤ ((((t.prod id : ℕ)) : ℝ) / Q0) ^ σ := by
      refine Real.one_le_rpow (le_of_lt ?_) hσ.le
      rw [lt_div_iff₀ hQ0]
      linarith
    have heq : Q0 ^ (-σ) * ((((t.prod id : ℕ)) : ℝ) ^ σ)
        = ((((t.prod id : ℕ)) : ℝ) / Q0) ^ σ := by
      rw [Real.rpow_neg hQ0.le, Real.div_rpow hX hQ0.le]
      field_simp
    have hprodw : (0 : ℝ) ≤ ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2 :=
      Finset.prod_nonneg (fun p hp => hw p (Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1 hp))
    calc ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2
        = 1 * ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2 := (one_mul _).symm
      _ ≤ (Q0 ^ (-σ) * ((((t.prod id : ℕ)) : ℝ) ^ σ))
            * ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ hprodw
          rw [heq]
          exact hge
  refine (Finset.sum_le_sum hpt).trans ?_
  -- drop the filter, keeping nonnegativity
  have hsub : s.powerset.filter (fun t => Q0 < ((t.prod id : ℕ) : ℝ)) ⊆ s.powerset :=
    Finset.filter_subset _ _
  have hnonneg : ∀ t ∈ s.powerset, t ∉ s.powerset.filter (fun t => Q0 < ((t.prod id : ℕ) : ℝ)) →
      (0 : ℝ) ≤ Q0 ^ (-σ) * ((((t.prod id : ℕ)) : ℝ) ^ σ)
        * ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2 := by
    intro t ht _
    have h1 : (0 : ℝ) ≤ Q0 ^ (-σ) := Real.rpow_nonneg hQ0.le _
    have h2 : (0 : ℝ) ≤ ((((t.prod id : ℕ)) : ℝ) ^ σ) := Real.rpow_nonneg (by positivity) _
    have h3 : (0 : ℝ) ≤ ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2 :=
      Finset.prod_nonneg (fun p hp => hw p (Finset.mem_powerset.mp ht hp))
    positivity
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg).trans ?_
  have hcongr : (∑ t ∈ s.powerset, Q0 ^ (-σ) * ((((t.prod id : ℕ)) : ℝ) ^ σ)
        * ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2)
      = ∑ t ∈ s.powerset, Q0 ^ (-σ) * (((((t.prod id : ℕ)) : ℝ) ^ σ)
        * ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2) :=
    Finset.sum_congr rfl (fun t _ => by ring)
  rw [hcongr, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hQ0.le _)
  have hexp : (∑ t ∈ s.powerset, ((((t.prod id : ℕ)) : ℝ) ^ σ)
        * ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2)
      = ∑ t ∈ s.powerset, ∏ p ∈ t, ((p : ℝ) ^ σ * (((p : ℝ) + 6) / (p : ℝ) ^ 2)) := by
    refine Finset.sum_congr rfl (fun t ht => ?_)
    have hcast : ((((t.prod id : ℕ)) : ℝ)) = ∏ p ∈ t, (p : ℝ) := by push_cast; rfl
    rw [hcast, ← Real.finsetProd_rpow t (fun p => (p : ℝ))
      (fun p _ => Nat.cast_nonneg p) σ, Finset.prod_mul_distrib]
  rw [hexp, prod_add_expansion]


/-- `prod (1 + y) <= exp (sum y)` for nonnegative `y`. -/
private lemma prod_one_add_le_exp (s : Finset ℕ) (y : ℕ → ℝ) (hy : ∀ p ∈ s, 0 ≤ y p) :
    ∏ p ∈ s, (1 + y p) ≤ Real.exp (∑ p ∈ s, y p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Real.exp_add]
    have h1 : 1 + y a ≤ Real.exp (y a) := by
      simpa [add_comm] using Real.add_one_le_exp (y a)
    have h2 : ∏ p ∈ s, (1 + y p) ≤ Real.exp (∑ p ∈ s, y p) :=
      ih (fun p hp => hy p (Finset.mem_insert_of_mem hp))
    have h3 : (0 : ℝ) ≤ ∏ p ∈ s, (1 + y p) :=
      Finset.prod_nonneg (fun p hp => by
        have := hy p (Finset.mem_insert_of_mem hp); linarith)
    exact mul_le_mul h1 h2 h3 (Real.exp_nonneg _)

/-- The `sigma`-shifted weight is at most `7 p^(sigma-1)`. -/
private lemma weight_pow_le (p : ℕ) (hp : p.Prime) (σ : ℝ) (hσ : 0 ≤ σ) :
    (p : ℝ) ^ σ * (((p : ℝ) + 6) / (p : ℝ) ^ 2) ≤ 7 * (p : ℝ) ^ (σ - 1) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hkey : (p : ℝ) ^ σ * (((p : ℝ) + 6) / (p : ℝ) ^ 2)
      = (p : ℝ) ^ (σ - 1) * (1 + 6 / (p : ℝ)) := by
    rw [Real.rpow_sub hp0 σ 1, Real.rpow_one]
    field_simp
    try ring
  rw [hkey]
  have hnon : (0 : ℝ) ≤ (p : ℝ) ^ (σ - 1) := Real.rpow_nonneg hp0.le _
  have h6 : 1 + 6 / (p : ℝ) ≤ 7 := by
    have : 0 < (p : ℝ) := hp0
    have hle : 6 / (p : ℝ) ≤ 3 := by
      rw [div_le_iff₀ hp0]; linarith
    linarith
  calc (p : ℝ) ^ (σ - 1) * (1 + 6 / (p : ℝ))
      ≤ (p : ℝ) ^ (σ - 1) * 7 := mul_le_mul_of_nonneg_left h6 hnon
    _ = 7 * (p : ℝ) ^ (σ - 1) := by ring

/-- The Euler product of the Rankin step, bounded by an exponential of the
prime-reciprocal sum. -/
private lemma euler_product_le (s : Finset ℕ) (hprime : ∀ p ∈ s, p.Prime) (σ : ℝ) (hσ : 0 ≤ σ) :
    ∏ p ∈ s, (1 + (p : ℝ) ^ σ * (((p : ℝ) + 6) / (p : ℝ) ^ 2))
      ≤ Real.exp (7 * ∑ p ∈ s, (p : ℝ) ^ (σ - 1)) := by
  classical
  refine (prod_one_add_le_exp s
    (fun p => (p : ℝ) ^ σ * (((p : ℝ) + 6) / (p : ℝ) ^ 2)) ?_).trans ?_
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).two_le
    positivity
  · refine Real.exp_le_exp.mpr ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun p hp => ?_)
    exact weight_pow_le p (hprime p hp) σ hσ

/-! ### The prime-reciprocal sum and the smooth tail -/

/-- The step `1/(K+1) ≤ log(K+1) - log K` for `K ≥ 1`. -/
private lemma one_div_succ_le_log_sub (K : ℕ) (hK : 1 ≤ K) :
    1 / ((K : ℝ) + 1) ≤ Real.log ((K : ℝ) + 1) - Real.log (K : ℝ) := by
  have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have h := Real.one_sub_inv_le_log_of_pos (x := ((K : ℝ) + 1) / (K : ℝ)) (by positivity)
  rw [Real.log_div (by positivity) (ne_of_gt hK0)] at h
  have hinv : (((K : ℝ) + 1) / (K : ℝ))⁻¹ = 1 - 1 / ((K : ℝ) + 1) := by
    field_simp
    ring
  rw [hinv] at h
  linarith

/-- Harmonic sum: `∑_{k<K} 1/(k+1) ≤ 1 + log K`. -/
private lemma sum_range_one_div_add_one_le (K : ℕ) :
    (∑ k ∈ Finset.range K, 1 / ((k : ℝ) + 1)) ≤ 1 + Real.log K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK; norm_num
    · have hstep := one_div_succ_le_log_sub K hK
      have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith

/-- `∑_{j=1}^{K} 1/j ≤ 1 + log K`. -/
private lemma sum_Icc_one_div_le (K : ℕ) :
    (∑ j ∈ Finset.Icc 1 K, 1 / (j : ℝ)) ≤ 1 + Real.log K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK; norm_num
    · rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1)]
      have hstep := one_div_succ_le_log_sub K hK
      have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith

/-- Chebyshev bounds the number of primes in a dyadic block. -/
private lemma card_primes_block_le (k : ℕ) (hk : 1 ≤ k) (s : Finset ℕ)
    (hsp : ∀ p ∈ s, p.Prime) (hlo : ∀ p ∈ s, 2 ^ k ≤ p) (hhi : ∀ p ∈ s, p ≤ 2 ^ (k + 1)) :
    (s.card : ℝ) ≤ Real.log 4 * (2 : ℝ) ^ (k + 1) / ((k : ℝ) * Real.log 2) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hpt : ∀ p ∈ s, (k : ℝ) * Real.log 2 ≤ Real.log (p : ℝ) := by
    intro p hp
    have hp2 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hcast : (((2 ^ k : ℕ)) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
    have hkp : (2 : ℝ) ^ k ≤ (p : ℝ) := by
      have h : (((2 ^ k : ℕ)) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hlo p hp
      rwa [hcast] at h
    have h := Real.log_le_log hp2 hkp
    rwa [Real.log_pow] at h
  have hsum : (s.card : ℝ) * ((k : ℝ) * Real.log 2) ≤ ∑ p ∈ s, Real.log (p : ℝ) := by
    have h := Finset.sum_le_sum hpt
    simpa [Finset.sum_const, nsmul_eq_mul] using h
  have htheta : (∑ p ∈ s, Real.log (p : ℝ)) ≤ Real.log 4 * (((2 ^ (k + 1) : ℕ)) : ℝ) := by
    have hsub : s ⊆ Nat.primesLE (2 ^ (k + 1)) := by
      intro p hp
      exact Nat.mem_primesLE.mpr ⟨hhi p hp, hsp p hp⟩
    have h1 : (∑ p ∈ s, Real.log (p : ℝ))
        ≤ ∑ p ∈ Nat.primesLE (2 ^ (k + 1)), Real.log (p : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
      intro p hp _
      exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)
    rw [← Chebyshev.theta_eq_sum_primesLE_log (2 ^ (k + 1))] at h1
    have h3 := Chebyshev.theta_le_log4_mul_x
      (x := (((2 ^ (k + 1) : ℕ)) : ℝ)) (by positivity)
    linarith
  have hcast2 : (((2 ^ (k + 1) : ℕ)) : ℝ) = (2 : ℝ) ^ (k + 1) := by push_cast; ring
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) * Real.log 2)]
  calc (s.card : ℝ) * ((k : ℝ) * Real.log 2) ≤ ∑ p ∈ s, Real.log (p : ℝ) := hsum
    _ ≤ Real.log 4 * (((2 ^ (k + 1) : ℕ)) : ℝ) := htheta
    _ = Real.log 4 * (2 : ℝ) ^ (k + 1) := by rw [hcast2]

/-- `2 ^ Nat.log2 z ≤ z < 2 ^ (Nat.log2 z + 1)`. -/
private lemma log2_spec {z : ℕ} (hz : 0 < z) : 2 ^ Nat.log2 z ≤ z ∧ z < 2 ^ (Nat.log2 z + 1) := by
  refine ⟨(Nat.le_log2 hz.ne').mp le_rfl, ?_⟩
  by_contra hcon
  simp only [not_lt] at hcon
  have hle := (Nat.le_log2 hz.ne').mpr hcon
  omega

/-- Weak Mertens: the reciprocal prime sum is at most a constant times `log log`. -/
private lemma prime_sum_inv_le (z : ℕ) (hz : 2 ≤ z) :
    (∑ p ∈ Nat.primesLE z, 1 / (p : ℝ)) ≤ 40 * (1 + Real.log (1 + Real.log z)) := by
  classical
  have hz0 : z ≠ 0 := by omega
  have hz1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 1 < z)
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos hz1
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hKspec := log2_spec (z := z) (by omega : 0 < z)
  obtain ⟨h2K, -⟩ := hKspec
  have hmaps : ∀ p ∈ Nat.primesLE z, Nat.log2 p ∈ Finset.Icc 1 (Nat.log2 z) := by
    intro p hp
    obtain ⟨hpz, hpp⟩ := Nat.mem_primesLE.mp hp
    have hpne : p ≠ 0 := hpp.ne_zero
    have h2p : 2 ^ Nat.log2 p ≤ p := (Nat.le_log2 hpne).mp le_rfl
    have h2z : 2 ^ Nat.log2 p ≤ z := le_trans h2p hpz
    refine Finset.mem_Icc.mpr ⟨?_, (Nat.le_log2 hz0).mpr h2z⟩
    rw [Nat.le_log2 hpne]
    calc 2 ^ 1 = 2 := by norm_num
      _ ≤ p := hpp.two_le
  have hfiber : ∀ j ∈ Finset.Icc 1 (Nat.log2 z),
      (∑ p ∈ (Nat.primesLE z).filter (fun p => Nat.log2 p = j), 1 / (p : ℝ)) ≤ 6 / (j : ℝ) := by
    intro j hj
    obtain ⟨hj1, hjK⟩ := Finset.mem_Icc.mp hj
    have hsp : ∀ p ∈ (Nat.primesLE z).filter (fun p => Nat.log2 p = j), p.Prime :=
      fun p hp => (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
    have hlo : ∀ p ∈ (Nat.primesLE z).filter (fun p => Nat.log2 p = j), 2 ^ j ≤ p := by
      intro p hp
      have hpe : Nat.log2 p = j := (Finset.mem_filter.mp hp).2
      have hpne : p ≠ 0 := (hsp p hp).ne_zero
      rw [← hpe]
      exact (Nat.le_log2 hpne).mp le_rfl
    have hhi : ∀ p ∈ (Nat.primesLE z).filter (fun p => Nat.log2 p = j), p ≤ 2 ^ (j + 1) := by
      intro p hp
      have hpe : Nat.log2 p = j := (Finset.mem_filter.mp hp).2
      have hpne : p ≠ 0 := (hsp p hp).ne_zero
      have hlt : p < 2 ^ (Nat.log2 p + 1) := (log2_spec hpne.bot_lt).2
      rw [hpe] at hlt
      omega
    have hcard := card_primes_block_le j hj1 _ hsp hlo hhi
    have hpoint : ∀ p ∈ (Nat.primesLE z).filter (fun p => Nat.log2 p = j),
        1 / (p : ℝ) ≤ 1 / (2 : ℝ) ^ j := by
      intro p hp
      have hp2 : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
      have hpj : (2 : ℝ) ^ j ≤ (p : ℝ) := by
        have hcast : (((2 ^ j : ℕ)) : ℝ) = (2 : ℝ) ^ j := by push_cast; ring
        have h : (((2 ^ j : ℕ)) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hlo p hp
        rwa [hcast] at h
      exact one_div_le_one_div_of_le hp2 hpj
    have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have h2j : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    calc (∑ p ∈ (Nat.primesLE z).filter (fun p => Nat.log2 p = j), 1 / (p : ℝ))
        ≤ ∑ _p ∈ (Nat.primesLE z).filter (fun p => Nat.log2 p = j), 1 / (2 : ℝ) ^ j :=
          Finset.sum_le_sum hpoint
      _ = (((Nat.primesLE z).filter (fun p => Nat.log2 p = j)).card : ℝ) * (1 / (2 : ℝ) ^ j) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ = (((Nat.primesLE z).filter (fun p => Nat.log2 p = j)).card : ℝ) / (2 : ℝ) ^ j := by ring
      _ ≤ (Real.log 4 * (2 : ℝ) ^ (j + 1) / ((j : ℝ) * Real.log 2)) / (2 : ℝ) ^ j :=
          div_le_div_of_nonneg_right hcard h2j.le
      _ = 4 / (j : ℝ) := by
          rw [hlog4]
          field_simp
          ring
      _ ≤ 6 / (j : ℝ) := div_le_div_of_nonneg_right (by norm_num) hjR.le
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun p => 1 / (p : ℝ))]
  have hKpos : 1 ≤ Nat.log2 z := by
    have hmem : Nat.log2 2 ∈ Finset.Icc 1 (Nat.log2 z) :=
      hmaps 2 (Nat.mem_primesLE.mpr ⟨hz, Nat.prime_two⟩)
    rw [show Nat.log2 2 = 1 by decide] at hmem
    exact (Finset.mem_Icc.mp hmem).2
  have hKle : ((Nat.log2 z : ℕ) : ℝ) * Real.log 2 ≤ Real.log z := by
    have hcast : (((2 ^ Nat.log2 z : ℕ)) : ℝ) = (2 : ℝ) ^ Nat.log2 z := by push_cast; ring
    have h : (((2 ^ Nat.log2 z : ℕ)) : ℝ) ≤ (z : ℝ) := by exact_mod_cast h2K
    rw [hcast] at h
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ Nat.log2 z := by positivity
    have hlog := Real.log_le_log h2pos h
    rw [Real.log_pow] at hlog
    exact hlog
  have hKle' : ((Nat.log2 z : ℕ) : ℝ) ≤ Real.log z / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    exact hKle
  have hloglog : Real.log ((Nat.log2 z : ℕ) : ℝ) ≤ Real.log (Real.log z) + 1 := by
    have hKR : (0 : ℝ) < ((Nat.log2 z : ℕ) : ℝ) := by exact_mod_cast hKpos
    have h1 : Real.log ((Nat.log2 z : ℕ) : ℝ) ≤ Real.log (Real.log z / Real.log 2) :=
      Real.log_le_log hKR hKle'
    rw [Real.log_div hlogz.ne' hlog2.ne'] at h1
    have h2 : -Real.log (Real.log 2) ≤ 1 := by
      have hexp : Real.exp (-1) < Real.log 2 := by
        have h1 : Real.exp (-1) < 0.4 := by
          rw [Real.exp_neg]
          rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num : (0:ℝ) < 0.4)]
          have := Real.exp_one_gt_d9
          norm_num
          linarith
        linarith [Real.log_two_gt_d9]
      have h3 := Real.le_log_iff_exp_le hlog2 |>.mpr hexp.le
      linarith
    linarith
  have hlog1 : Real.log (1 + Real.log z) ≥ 0 := Real.log_nonneg (by linarith)
  calc (∑ j ∈ Finset.Icc 1 (Nat.log2 z),
        ∑ p ∈ (Nat.primesLE z).filter (fun p => Nat.log2 p = j), 1 / (p : ℝ))
      ≤ ∑ j ∈ Finset.Icc 1 (Nat.log2 z), 6 / (j : ℝ) := Finset.sum_le_sum hfiber
    _ = 6 * ∑ j ∈ Finset.Icc 1 (Nat.log2 z), 1 / (j : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ 6 * (1 + Real.log ((Nat.log2 z : ℕ) : ℝ)) := by
        have := sum_Icc_one_div_le (Nat.log2 z)
        linarith
    _ ≤ 40 * (1 + Real.log (1 + Real.log z)) := by
        have hLL : Real.log (Real.log z) ≤ Real.log (1 + Real.log z) :=
          Real.log_le_log hlogz (by linarith)
        linarith

/-- The elementary bound `log u ≤ u^t / t` at `u ≥ 1`. -/
private lemma log_le_rpow_div {u t : ℝ} (hu : 1 ≤ u) (ht : 0 < t) :
    Real.log u ≤ u ^ t / t := by
  have hu0 : (0 : ℝ) < u := by linarith
  have h1 : Real.log (u ^ t) = t * Real.log u := Real.log_rpow hu0 t
  have h2 : Real.log (u ^ t) ≤ u ^ t - 1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hu0 t)
  have hut : (1 : ℝ) ≤ u ^ t := Real.one_le_rpow hu ht.le
  rw [le_div_iff₀ ht]
  nlinarith [h1, h2]


/-- `log u + 2 ≤ 6 u^(ε/4)/ε` for `u ≥ 1`, `0 < ε ≤ 1`. -/
private lemma logu_add_two_le {u ε : ℝ} (hu : 1 ≤ u) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Real.log u + 2 ≤ 6 * u ^ (ε / 4) / ε := by
  have hu0 : (0 : ℝ) < u := by linarith
  have ht : (0 : ℝ) < ε / 4 := by linarith
  have hP : (0 : ℝ) < u ^ (ε / 4) := Real.rpow_pos_of_pos hu0 _
  have h1 : Real.log u ≤ u ^ (ε / 4) / (ε / 4) := log_le_rpow_div hu ht
  have h2 : u ^ (ε / 4) / (ε / 4) = 4 * u ^ (ε / 4) / ε := by field_simp
  rw [h2] at h1
  have h3 : (1 : ℝ) ≤ u ^ (ε / 4) := Real.one_le_rpow hu ht.le
  have h5 : 2 ≤ 2 * u ^ (ε / 4) / ε := by
    rw [le_div_iff₀ hε]
    nlinarith [hP, h3, hε1]
  have h7 : 4 * u ^ (ε / 4) / ε + 2 * u ^ (ε / 4) / ε = 6 * u ^ (ε / 4) / ε := by ring
  linarith

/-- `(X^(4/(3ε)))^((3ε)/4) = X`. -/
private lemma rpow_mul_self {X ε : ℝ} (hX : 0 ≤ X) (hε : 0 < ε) :
    (X ^ (4 / (3 * ε))) ^ ((3 * ε) / 4) = X := by
  rw [← Real.rpow_mul hX]
  rw [show 4 / (3 * ε) * ((3 * ε) / 4) = 1 by field_simp]
  rw [Real.rpow_one]

/-- Crossing a `rpow` threshold: `u ≥ X^(4/(3ε))` gives `X ≤ u^((3ε)/4)`. -/
private lemma rpow_threshold {X ε u : ℝ} (hX : 0 ≤ X) (hε : 0 < ε)
    (hu : X ^ (4 / (3 * ε)) ≤ u) : X ≤ u ^ ((3 * ε) / 4) := by
  have h1 : (X ^ (4 / (3 * ε))) ^ ((3 * ε) / 4) ≤ u ^ ((3 * ε) / 4) := by
    apply Real.rpow_le_rpow (Real.rpow_nonneg hX _) hu
    positivity
  rwa [rpow_mul_self hX hε] at h1


/-- Stage 1 of the assembly: the remainder is bounded by the numerical majorant of
the `A2` mass of the subset tail above `Q0`. -/
private lemma remainder_le_majorant (n : ℕ) (P Q Q0 : ℝ) (hQ : 0 ≤ Q) (hP : 0 < P)
    (hPQ : P ≤ Q) :
    ‖(LeanLab.KumchevLiu2007.Task129.series2 n P - LeanLab.KumchevLiu2007.Task129b.product2 n Q)
        - LeanLab.KumchevLiu2007.Task129b.tail2 n P Q0 Q‖
      ≤ ∑ t ∈ ((Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime).powerset.filter
          (fun t => (⌊Q0⌋₊ : ℝ) < (((t.prod id : ℕ)) : ℝ)),
          ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2 := by
  classical
  have hΔ := rem_eq_subset_tail n P Q Q0 hQ hP hPQ
  rw [hΔ, norm_neg]
  refine (norm_sum_le _ _).trans ?_
  set S : Finset ℕ := (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime with hSdef
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hsub : S.powerset.filter (fun t => max ⌊P⌋₊ ⌊Q0⌋₊ < t.prod id)
      ⊆ S.powerset.filter (fun t => (⌊Q0⌋₊ : ℝ) < (((t.prod id : ℕ)) : ℝ)) := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := Finset.mem_filter.mp ht
    refine Finset.mem_filter.mpr ⟨ht1, ?_⟩
    have hmax : ⌊Q0⌋₊ ≤ max ⌊P⌋₊ ⌊Q0⌋₊ := le_max_right _ _
    have h2 : (((max ⌊P⌋₊ ⌊Q0⌋₊ : ℕ)) : ℝ) < (((t.prod id : ℕ)) : ℝ) := by exact_mod_cast ht2
    have h3 : (((⌊Q0⌋₊ : ℕ)) : ℝ) ≤ (((max ⌊P⌋₊ ⌊Q0⌋₊ : ℕ)) : ℝ) := by exact_mod_cast hmax
    linarith
  have hnn : ∀ t ∈ S.powerset.filter (fun t => (⌊Q0⌋₊ : ℝ) < (((t.prod id : ℕ)) : ℝ)),
      t ∉ S.powerset.filter (fun t => max ⌊P⌋₊ ⌊Q0⌋₊ < t.prod id) →
      (0 : ℝ) ≤ ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2 := by
    intro t ht _
    refine Finset.prod_nonneg (fun p hp => ?_)
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (hprime p (Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1 hp)).two_le
    positivity
  calc (∑ t ∈ S.powerset.filter (fun t => max ⌊P⌋₊ ⌊Q0⌋₊ < t.prod id),
        ‖U1534.A2 n (t.prod id)‖)
      ≤ ∑ t ∈ S.powerset.filter (fun t => max ⌊P⌋₊ ⌊Q0⌋₊ < t.prod id),
          ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2 := by
        refine Finset.sum_le_sum (fun t ht => ?_)
        exact A2_norm_le n t
          (fun p hp => hprime p (Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1 hp))
    _ ≤ ∑ t ∈ S.powerset.filter (fun t => (⌊Q0⌋₊ : ℝ) < (((t.prod id : ℕ)) : ℝ)),
          ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub hnn


/-- Stage 2 of the assembly: Rankin's trick, the Euler product expansion and the weak
Mertens bound give the tail majorant in terms of an arbitrary Rankin parameter `σ`. -/
private lemma majorant_le {Q Q0 : ℝ} (hQ1 : 1 ≤ Q) (hQ0 : 1 ≤ Q0) {σ : ℝ} (hσ : 0 < σ) :
    (∑ t ∈ ((Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime).powerset.filter
        (fun t => (⌊Q0⌋₊ : ℝ) < (((t.prod id : ℕ)) : ℝ)),
        ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2)
      ≤ Real.exp (-(σ * Real.log (((⌊Q0⌋₊ : ℕ)) : ℝ))
          + 7 * (Real.exp (σ * Real.log (((⌊Q⌋₊ + 1 : ℕ)) : ℝ))
            * (40 * (1 + Real.log (1 + Real.log (((⌊Q⌋₊ + 1 : ℕ)) : ℝ)))))) := by
  classical
  set S : Finset ℕ := (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime with hSdef
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  set z : ℕ := ⌊Q⌋₊ + 1 with hzdef
  have hz2 : 2 ≤ z := by
    have h1 : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by exact_mod_cast hQ1)
    omega
  set L : ℝ := Real.log z with hLdef
  have hLpos : 0 < L := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hQ0pos : (0 : ℝ) < (((⌊Q0⌋₊ : ℕ)) : ℝ) := by
    have h1 : 1 ≤ ⌊Q0⌋₊ := Nat.le_floor (by exact_mod_cast hQ0)
    exact_mod_cast (by omega : 0 < ⌊Q0⌋₊)
  have hSsub : S ⊆ Nat.primesLE z := by
    intro p hp
    have hp1 := Finset.mem_filter.mp hp
    have hplt : p < z := by
      have := Finset.mem_range.mp hp1.1
      omega
    exact Nat.mem_primesLE.mpr ⟨le_of_lt hplt, hp1.2⟩
  -- `p^(σ-1) ≤ exp(σ L)/p` for `p ∈ S`
  have hterm : ∀ p ∈ S, (p : ℝ) ^ (σ - 1) ≤ Real.exp (σ * L) * (1 / (p : ℝ)) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hprime p hp).two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hpz : (p : ℝ) ≤ (z : ℝ) := by
      have hplt : p < z := by
        have := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
        omega
      exact_mod_cast le_of_lt hplt
    have hlogp : Real.log (p : ℝ) ≤ L := by
      rw [hLdef]
      exact Real.log_le_log hp0 hpz
    have hmono : Real.exp (Real.log (p : ℝ) * σ) ≤ Real.exp (L * σ) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hlogp, hσ.le]
    have hsplit : (p : ℝ) ^ (σ - 1) = (p : ℝ) ^ σ / (p : ℝ) := by
      rw [Real.rpow_sub hp0 σ 1, Real.rpow_one]
    have h2 : (p : ℝ) ^ σ / (p : ℝ) ≤ Real.exp (L * σ) / (p : ℝ) := by
      refine div_le_div_of_nonneg_right ?_ hp0.le
      rw [Real.rpow_def_of_pos hp0 σ]
      exact hmono
    rw [hsplit]
    calc (p : ℝ) ^ σ / (p : ℝ) ≤ Real.exp (L * σ) / (p : ℝ) := h2
      _ = Real.exp (σ * L) * (1 / (p : ℝ)) := by
          rw [mul_comm L σ, div_eq_mul_one_div]
  have hPsum : (∑ p ∈ S, (p : ℝ) ^ (σ - 1))
      ≤ Real.exp (σ * L) * (40 * (1 + Real.log (1 + L))) := by
    have h1 : (∑ p ∈ S, (p : ℝ) ^ (σ - 1))
        ≤ ∑ p ∈ S, Real.exp (σ * L) * (1 / (p : ℝ)) := Finset.sum_le_sum hterm
    have h2 : (∑ p ∈ S, Real.exp (σ * L) * (1 / (p : ℝ)))
        = Real.exp (σ * L) * ∑ p ∈ S, 1 / (p : ℝ) := by
      rw [Finset.mul_sum]
    have h3 : (∑ p ∈ S, 1 / (p : ℝ)) ≤ ∑ p ∈ Nat.primesLE z, 1 / (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun p hp _ => by positivity)
    have h4 := prime_sum_inv_le z hz2
    have h6 : (∑ p ∈ S, 1 / (p : ℝ)) ≤ 40 * (1 + Real.log (1 + Real.log z)) := h3.trans h4
    have h7 : Real.log (1 + Real.log z) = Real.log (1 + L) := by rw [hLdef]
    rw [h7] at h6
    calc (∑ p ∈ S, (p : ℝ) ^ (σ - 1))
        ≤ ∑ p ∈ S, Real.exp (σ * L) * (1 / (p : ℝ)) := h1
      _ = Real.exp (σ * L) * ∑ p ∈ S, 1 / (p : ℝ) := h2
      _ ≤ Real.exp (σ * L) * (40 * (1 + Real.log (1 + L))) :=
          mul_le_mul_of_nonneg_left h6 (Real.exp_pos _).le
  have hRankin := subset_tail_rankin S hprime (((⌊Q0⌋₊ : ℕ)) : ℝ) hQ0pos σ hσ
  have hEuler := euler_product_le S hprime σ hσ.le
  have hQ0pow : (((⌊Q0⌋₊ : ℕ)) : ℝ) ^ (-σ) = Real.exp (-(σ * Real.log (((⌊Q0⌋₊ : ℕ)) : ℝ))) := by
    rw [Real.rpow_def_of_pos hQ0pos]
    congr 1
    ring
  have hLz : L = Real.log (((⌊Q⌋₊ + 1 : ℕ)) : ℝ) := by
    rw [hLdef, hzdef]
  calc (∑ t ∈ ((Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime).powerset.filter
        (fun t => (⌊Q0⌋₊ : ℝ) < (((t.prod id : ℕ)) : ℝ)),
        ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2)
      ≤ (((⌊Q0⌋₊ : ℕ)) : ℝ) ^ (-σ) *
          ∏ p ∈ S, (1 + (p : ℝ) ^ σ * (((p : ℝ) + 6) / (p : ℝ) ^ 2)) := hRankin
    _ ≤ (((⌊Q0⌋₊ : ℕ)) : ℝ) ^ (-σ) *
          Real.exp (7 * ∑ p ∈ S, (p : ℝ) ^ (σ - 1)) :=
        mul_le_mul_of_nonneg_left hEuler (Real.rpow_nonneg hQ0pos.le _)
    _ ≤ (((⌊Q0⌋₊ : ℕ)) : ℝ) ^ (-σ) *
          Real.exp (7 * (Real.exp (σ * L) * (40 * (1 + Real.log (1 + L))))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hQ0pos.le _)
        exact Real.exp_le_exp.mpr (by linarith [hPsum])
    _ = Real.exp (-(σ * Real.log (((⌊Q0⌋₊ : ℕ)) : ℝ))) *
          Real.exp (7 * (Real.exp (σ * L) * (40 * (1 + Real.log (1 + L))))) := by
        rw [hQ0pow]
    _ = Real.exp (-(σ * Real.log (((⌊Q0⌋₊ : ℕ)) : ℝ))
          + 7 * (Real.exp (σ * L) * (40 * (1 + Real.log (1 + L))))) :=
        (Real.exp_add _ _).symm
    _ = Real.exp (-(σ * Real.log (((⌊Q0⌋₊ : ℕ)) : ℝ))
          + 7 * (Real.exp (σ * Real.log (((⌊Q⌋₊ + 1 : ℕ)) : ℝ))
            * (40 * (1 + Real.log (1 + Real.log (((⌊Q⌋₊ + 1 : ℕ)) : ℝ)))))) := by
        rw [hLz]


/-- Monotonicity of `u ^ ·` for `u ≥ 1`. -/
private lemma rpow_le_rpow_of_le_one {u a b : ℝ} (hu : 1 ≤ u) (hab : a ≤ b) :
    u ^ a ≤ u ^ b := by
  rcases lt_or_eq_of_le hu with h | h
  · exact (Real.rpow_le_rpow_left_iff h).mpr hab
  · subst h
    simp

/-- Stage 3a: `1 + log (1 + L) ≤ log u + 2` in the Lemma 3.8 range. -/
private lemma one_add_log_le {ε u L : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hu : 2 ≤ u)
    (hL : 0 < L) (hLb : L ≤ 2 * u ^ (1 - ε)) : 1 + Real.log (1 + L) ≤ Real.log u + 2 := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hu1 : (1 : ℝ) ≤ u := by linarith
  have h1 : u ^ (1 - ε) ≤ u := by
    calc u ^ (1 - ε) ≤ u ^ (1 : ℝ) := rpow_le_rpow_of_le_one hu1 (by linarith)
      _ = u := Real.rpow_one u
  have h2 : 1 + L ≤ (5 / 2) * u := by linarith
  have h3 : Real.log (1 + L) ≤ Real.log ((5 / 2) * u) := Real.log_le_log (by linarith) h2
  have h4 : Real.log ((5 / 2) * u) = Real.log (5 / 2) + Real.log u :=
    Real.log_mul (by norm_num) (ne_of_gt hu0)
  have h5 : Real.log (5 / 2) < 1 := by
    have h6 : Real.log (5 / 2) < Real.log (Real.exp 1) := by
      refine Real.log_lt_log (by norm_num) ?_
      linarith [Real.exp_one_gt_d9]
    rwa [Real.log_exp] at h6
  rw [h4] at h3
  linarith

/-- Stage 3b: the Rankin parameter is small enough, `σ L ≤ 1`. -/
private lemma sigma_mul_le_one {A ε u L M : ℝ} (hA : 2 ≤ A) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hu : 2 ≤ u) (hL : 0 < L) (hM : 0 < M)
    (hLb : L ≤ 2 * u ^ (1 - ε)) (hMb : (ε / 6) * u ≤ M)
    (hthr : 400 * (A + 1000) / ε ^ 2 ≤ u ^ ((3 * ε) / 4)) :
    2 * (A * Real.log u + 800 * (1 + Real.log (1 + L)) + 2) * L ≤ M := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hu1 : (1 : ℝ) ≤ u := by linarith
  have hlu : Real.log u + 2 ≤ 6 * u ^ (ε / 4) / ε := logu_add_two_le hu1 hε hε1
  have hA1 : 1 + Real.log (1 + L) ≤ Real.log u + 2 := one_add_log_le hε hε1 hu hL hLb
  -- step 1: `2 T ≤ (2A+1604)(log u + 2)`
  have hT2 : 2 * (A * Real.log u + 800 * (1 + Real.log (1 + L)) + 2)
      ≤ (2 * A + 1604) * (Real.log u + 2) := by
    have h1 : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu1
    have h2 : (0 : ℝ) ≤ A := by linarith
    have h3 : 800 * (1 + Real.log (1 + L)) ≤ 800 * (Real.log u + 2) :=
      mul_le_mul_of_nonneg_left hA1 (by norm_num)
    nlinarith [h3, h1, h2]
  -- step 2: multiply by `L ≤ 2 u^(1-ε)`
  have hpow1 : (0 : ℝ) < u ^ (ε / 4) := Real.rpow_pos_of_pos hu0 _
  have hpow2 : (0 : ℝ) < u ^ (1 - ε) := Real.rpow_pos_of_pos hu0 _
  have hmid : 2 * (A * Real.log u + 800 * (1 + Real.log (1 + L)) + 2) * L
      ≤ (2 * A + 1604) * (6 * u ^ (ε / 4) / ε) * (2 * u ^ (1 - ε)) := by
    have h1 : (0 : ℝ) ≤ 2 * A + 1604 := by linarith
    have h2 : (0 : ℝ) < 6 * u ^ (ε / 4) / ε := by positivity
    have h3 : (0 : ℝ) < 2 * u ^ (1 - ε) := by positivity
    have h4 : 2 * (A * Real.log u + 800 * (1 + Real.log (1 + L)) + 2)
        ≤ (2 * A + 1604) * (6 * u ^ (ε / 4) / ε) :=
      hT2.trans (mul_le_mul_of_nonneg_left hlu h1)
    have h5 : 2 * (A * Real.log u + 800 * (1 + Real.log (1 + L)) + 2) * L
        ≤ ((2 * A + 1604) * (6 * u ^ (ε / 4) / ε)) * L :=
      mul_le_mul_of_nonneg_right h4 hL.le
    have h6 : ((2 * A + 1604) * (6 * u ^ (ε / 4) / ε)) * L
        ≤ ((2 * A + 1604) * (6 * u ^ (ε / 4) / ε)) * (2 * u ^ (1 - ε)) :=
      mul_le_mul_of_nonneg_left hLb (by positivity)
    linarith [h5, h6]
  -- step 3: the right hand side is at most `(ε/6) u`
  have hexp : (2 * A + 1604) * (6 * u ^ (ε / 4) / ε) * (2 * u ^ (1 - ε))
      = (12 * (2 * A + 1604) / ε) * (u ^ (ε / 4) * u ^ (1 - ε)) := by
    field_simp
    ring
  have hsplit : u ^ (ε / 4) * u ^ (1 - ε) = u ^ (1 - (3 * ε) / 4) := by
    rw [← Real.rpow_add hu0]
    congr 1
    ring
  have hkey : u ^ (1 - (3 * ε) / 4) * u ^ ((3 * ε) / 4) = u := by
    rw [← Real.rpow_add hu0]
    rw [show 1 - (3 * ε) / 4 + (3 * ε) / 4 = 1 by ring]
    rw [Real.rpow_one]
  have hw : (0 : ℝ) < u ^ ((3 * ε) / 4) := Real.rpow_pos_of_pos hu0 _
  have hcoef : 12 * (2 * A + 1604) / ε ≤ (ε / 6) * u ^ ((3 * ε) / 4) := by
    have h1 : 72 * (2 * A + 1604) / ε ^ 2 ≤ u ^ ((3 * ε) / 4) := by
      have h2 : 72 * (2 * A + 1604) ≤ 400 * (A + 1000) := by nlinarith
      have h3 : (0 : ℝ) < ε ^ 2 := by positivity
      calc 72 * (2 * A + 1604) / ε ^ 2 ≤ 400 * (A + 1000) / ε ^ 2 :=
            div_le_div_of_nonneg_right h2 h3.le
        _ ≤ u ^ ((3 * ε) / 4) := hthr
    have h5 : 12 * (2 * A + 1604) ≤ (ε ^ 2 / 6) * u ^ ((3 * ε) / 4) := by
      have h6 : (0 : ℝ) ≤ ε ^ 2 / 6 := by positivity
      have h7 := mul_le_mul_of_nonneg_left h1 h6
      have h8 : (ε ^ 2 / 6) * (72 * (2 * A + 1604) / ε ^ 2) = 12 * (2 * A + 1604) := by
        field_simp
        ring
      linarith [h7, h8]
    rw [div_le_iff₀ hε]
    nlinarith [h5]
  have hstep : (12 * (2 * A + 1604) / ε) * u ^ (1 - (3 * ε) / 4) ≤ (ε / 6) * u := by
    have h1 : (12 * (2 * A + 1604) / ε) * u ^ (1 - (3 * ε) / 4)
        ≤ ((ε / 6) * u ^ ((3 * ε) / 4)) * u ^ (1 - (3 * ε) / 4) :=
      mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hu0.le _)
    have h2 : ((ε / 6) * u ^ ((3 * ε) / 4)) * u ^ (1 - (3 * ε) / 4) = (ε / 6) * u := by
      rw [mul_assoc, ← Real.rpow_add hu0,
        show (3 * ε) / 4 + (1 - (3 * ε) / 4) = 1 by ring, Real.rpow_one]
    linarith [h1, h2]
  calc 2 * (A * Real.log u + 800 * (1 + Real.log (1 + L)) + 2) * L
      ≤ (2 * A + 1604) * (6 * u ^ (ε / 4) / ε) * (2 * u ^ (1 - ε)) := hmid
    _ = (12 * (2 * A + 1604) / ε) * (u ^ (ε / 4) * u ^ (1 - ε)) := hexp
    _ = (12 * (2 * A + 1604) / ε) * u ^ (1 - (3 * ε) / 4) := by rw [hsplit]
    _ ≤ (ε / 6) * u := hstep
    _ ≤ M := hMb


/-- Stage 4: the numerical endgame. With `σ M = 2 T`, `σ L ≤ 1` and
`T = A log log x + 800 (1 + log (1 + L)) + 2` the majorant is at most `(log x)^{-A}`. -/
private lemma exp_majorant_le {A u L M σ T : ℝ} (hA0 : 0 ≤ A) (hu : 1 ≤ u)
    (hX : 0 ≤ 1 + Real.log (1 + L)) (hσM : σ * M = 2 * T) (hσL : σ * L ≤ 1)
    (hT : T = A * Real.log u + 800 * (1 + Real.log (1 + L)) + 2) :
    Real.exp (-(σ * M) + 7 * (Real.exp (σ * L) * (40 * (1 + Real.log (1 + L)))))
      ≤ 1 / u ^ A := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu
  have h1 : Real.exp (σ * L) ≤ Real.exp 1 := Real.exp_le_exp.mpr hσL
  have h2 : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
  have h3 : 7 * (Real.exp (σ * L) * (40 * (1 + Real.log (1 + L))))
      ≤ 7 * (2.72 * (40 * (1 + Real.log (1 + L)))) := by
    have h4 : Real.exp (σ * L) * (40 * (1 + Real.log (1 + L)))
        ≤ 2.72 * (40 * (1 + Real.log (1 + L))) :=
      mul_le_mul_of_nonneg_right (le_trans h1 h2) (by linarith)
    linarith
  have h5 : -(σ * M) + 7 * (Real.exp (σ * L) * (40 * (1 + Real.log (1 + L))))
      ≤ -A * Real.log u - 1 := by
    rw [hσM, hT]
    nlinarith [h3, hlogu, hX, hA0]
  have h6 : Real.exp (-(σ * M) + 7 * (Real.exp (σ * L) * (40 * (1 + Real.log (1 + L)))))
      ≤ Real.exp (-A * Real.log u - 1) := Real.exp_le_exp.mpr h5
  have h7 : Real.exp (-A * Real.log u - 1) ≤ Real.exp (-A * Real.log u) := by
    apply Real.exp_le_exp.mpr
    linarith
  have h8 : Real.exp (-A * Real.log u) = u ^ (-A) := by
    rw [Real.rpow_def_of_pos hu0]
    congr 1
    ring
  have h9 : u ^ (-A) = 1 / u ^ A := by
    rw [Real.rpow_neg hu0.le, one_div]
  calc Real.exp (-(σ * M) + 7 * (Real.exp (σ * L) * (40 * (1 + Real.log (1 + L)))))
      ≤ Real.exp (-A * Real.log u - 1) := h6
    _ ≤ Real.exp (-A * Real.log u) := h7
    _ = u ^ (-A) := h8
    _ = 1 / u ^ A := h9


/-- Page 14 display 49. A real interval of length at least one contains
at most twice its length in natural numbers. -/
theorem interval_card_le {x y : ℝ} (hx : 0 ≤ x) (hy : 1 ≤ y) :
    ((intervalNumbers x y).card : ℝ) ≤ 2 * y := by
  rw [intervalNumbers, Nat.card_Ioc, Nat.cast_sub (Nat.floor_mono (by linarith : x ≤ x + y))]
  have hu := Nat.floor_le (by linarith : 0 ≤ x + y)
  have hl := Nat.sub_one_lt_floor x
  linarith

/-- LEAF. Page 14 display 50 and the smooth tail estimate below it.
Lemma 3.5 and display 47 give a uniform pointwise remainder with arbitrary
logarithmic decay. This is the square of that remainder bound. The tail
uses minus Psi from direct subtraction, as in the existing definition.
The analytic smooth number estimate remains OPEN. -/
theorem smooth_remainder_pointwise (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) → ∀ n : ℕ,
      ‖(series2 n P - product2 n Q) - tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2 ≤
        C / Real.log x ^ A := by
  classical
  set U : ℝ := max 8 (max ((400 * (A + 1000) / ε ^ 2) ^ (4 / (3 * ε)))
    (max (6 * Real.log 2 / ε) (3 * Real.log 2 / ε + 1))) with hUdef
  have hU8 : 8 ≤ U := le_max_left _ _
  have hUrpow : (400 * (A + 1000) / ε ^ 2) ^ (4 / (3 * ε)) ≤ U :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hUlog : 6 * Real.log 2 / ε ≤ U :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hU8e : 3 * Real.log 2 / ε + 1 ≤ U :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨1, Real.exp U, one_pos, ?_, ?_⟩
  · have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    calc (2 : ℝ) ≤ Real.exp 1 := h2
      _ ≤ Real.exp U := Real.exp_le_exp.mpr (by linarith)
  intro x y P Q hx hy hyx hP hPQ hQ n
  have hu : U ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos U) hx
    rwa [Real.log_exp] at h
  have hu1 : 1 ≤ Real.log x := by linarith
  have hu2 : 2 ≤ Real.log x := by linarith
  have hu0 : 0 < Real.log x := by linarith
  have hx1 : (1 : ℝ) < x := by
    have h2 := Real.exp_le_exp.mpr hU8
    have h3 : (1 : ℝ) < Real.exp 8 := by
      have h4 : Real.exp 0 < Real.exp 8 := Real.exp_lt_exp.mpr (by norm_num)
      simpa using h4
    linarith
  by_cases hεle : ε ≤ 1
  · -- main case `ε ≤ 1`
    have h1me : 0 ≤ 1 - ε := by linarith
    have hy1 : 1 ≤ y := by
      have h := Real.one_le_rpow hx1.le hε.le
      linarith
    have hy0 : 0 < y := by linarith
    have hQpos : (0 : ℝ) < Q := lt_of_lt_of_le hP hPQ
    have hQ0pos : 0 < ⌊y ^ (1 / 3 : ℝ)⌋₊ := by
      have h1 : (1 : ℝ) ≤ y ^ (1 / 3 : ℝ) := Real.one_le_rpow hy1 (by norm_num)
      exact Nat.le_floor (by exact_mod_cast h1)
    have hQ0R1 : (1 : ℝ) ≤ (((⌊y ^ (1 / 3 : ℝ)⌋₊ : ℕ)) : ℝ) := by exact_mod_cast hQ0pos
    have hstep := remainder_le_majorant n P Q (y ^ (1 / 3 : ℝ)) hQpos.le hP hPQ
    by_cases hQsmall : ⌊Q⌋₊ = 0
    · -- `S` is empty, so the remainder vanishes
      have hSempty : (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime = ∅ := by
        rw [hQsmall]
        decide
      have htail0 : (∑ t ∈ ((Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime).powerset.filter
          (fun t => (⌊y ^ (1 / 3 : ℝ)⌋₊ : ℝ) < (((t.prod id : ℕ)) : ℝ)),
          ∏ p ∈ t, ((p : ℝ) + 6) / (p : ℝ) ^ 2) = 0 := by
        refine Finset.sum_eq_zero (fun t ht => ?_)
        obtain ⟨ht1, ht2⟩ := Finset.mem_filter.mp ht
        rw [hSempty, Finset.powerset_empty, Finset.mem_singleton] at ht1
        subst ht1
        exact absurd ht2 (by
          simp only [Finset.prod_empty, Nat.cast_one]
          linarith)
      have hzero : ‖(LeanLab.KumchevLiu2007.Task129.series2 n P
            - LeanLab.KumchevLiu2007.Task129b.product2 n Q)
          - LeanLab.KumchevLiu2007.Task129b.tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ = 0 := by
        rw [htail0] at hstep
        exact le_antisymm hstep (norm_nonneg _)
      rw [hzero]
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
    · -- at least one prime below `Q`
      have hQ1 : 1 ≤ Q := by
        have h1 : 1 ≤ ⌊Q⌋₊ := by omega
        exact le_trans (by exact_mod_cast h1) (Nat.floor_le hQpos.le)
      set z : ℕ := ⌊Q⌋₊ + 1 with hzdef
      set L : ℝ := Real.log z with hLdef
      have hLpos : 0 < L := by
        rw [hLdef]
        exact Real.log_pos (by exact_mod_cast (by omega : 1 < z))
      have hlog1L : 0 ≤ Real.log (1 + L) := Real.log_nonneg (by linarith)
      set M : ℝ := Real.log (((⌊y ^ (1 / 3 : ℝ)⌋₊ : ℕ)) : ℝ) with hMdef
      set T : ℝ := A * Real.log (Real.log x) + 800 * (1 + Real.log (1 + L)) + 2 with hTdef
      have hlogu : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hu1
      -- `L ≤ 2 (log x)^(1-ε)`
      have hLb : L ≤ 2 * (Real.log x) ^ (1 - ε) := by
        have h1 : L = Real.log (z : ℝ) := by rw [hLdef]
        rw [h1]
        have hzQ : (z : ℝ) ≤ 2 * Q := by
          rw [hzdef]
          push_cast
          have h8 : ((⌊Q⌋₊ : ℕ) : ℝ) + 1 ≤ Q + 1 := by
            have := Nat.floor_le hQpos.le
            linarith
          nlinarith [hQ1]
        have h2 : Real.log (z : ℝ) ≤ Real.log (2 * Q) := Real.log_le_log (by positivity) hzQ
        have h3 : Real.log (2 * Q) = Real.log 2 + Real.log Q :=
          Real.log_mul (by norm_num) (ne_of_gt hQpos)
        rw [h3] at h2
        have h4 : Real.log Q ≤ Real.log x ^ (1 - ε) := by
          have h := Real.log_le_log hQpos hQ
          rwa [Real.log_exp] at h
        have h6 : (1 : ℝ) ≤ (Real.log x) ^ (1 - ε) := Real.one_le_rpow hu1 h1me
        have h5 : Real.log 2 ≤ (Real.log x) ^ (1 - ε) := by
          linarith [Real.log_two_lt_d9]
        linarith
      -- `M ≥ (ε/6) log x`
      have hMb : (ε / 6) * Real.log x ≤ M := by
        rw [hMdef]
        have h3 : Real.log (y ^ (1 / 3 : ℝ)) = (1 / 3 : ℝ) * Real.log y := Real.log_rpow hy0 _
        have h4 : (y ^ (1 / 3 : ℝ)) / 2 ≤ (((⌊y ^ (1 / 3 : ℝ)⌋₊ : ℕ)) : ℝ) := by
          have h5 : (1 : ℝ) ≤ y ^ (1 / 3 : ℝ) := Real.one_le_rpow hy1 (by norm_num)
          have h6 : y ^ (1 / 3 : ℝ) - 1 < (((⌊y ^ (1 / 3 : ℝ)⌋₊ : ℕ)) : ℝ) := by
            have h7 := Nat.lt_floor_add_one (y ^ (1 / 3 : ℝ))
            linarith
          linarith
        have h8 : Real.log ((y ^ (1 / 3 : ℝ)) / 2)
            ≤ Real.log ((((⌊y ^ (1 / 3 : ℝ)⌋₊ : ℕ)) : ℝ)) :=
          Real.log_le_log (by positivity) h4
        have h9 : Real.log ((y ^ (1 / 3 : ℝ)) / 2)
            = Real.log (y ^ (1 / 3 : ℝ)) - Real.log 2 := Real.log_div (by positivity) (by norm_num)
        rw [h9, h3] at h8
        have h11 : Real.log (x ^ ε) ≤ Real.log y := Real.log_le_log (by positivity) hy
        rw [Real.log_rpow (by linarith : (0 : ℝ) < x)] at h11
        have h13 : Real.log 2 ≤ (ε / 6) * Real.log x := by
          have h14 : 6 * Real.log 2 / ε ≤ Real.log x := le_trans hUlog hu
          rw [div_le_iff₀ hε] at h14
          nlinarith [h14, hε]
        linarith
      have hMpos : 0 < M := lt_of_lt_of_le (by positivity) hMb
      have hthr : 400 * (A + 1000) / ε ^ 2 ≤ (Real.log x) ^ ((3 * ε) / 4) :=
        rpow_threshold (by positivity) hε (hUrpow.trans hu)
      -- `σ L ≤ 1`
      have hTL : 2 * T * L ≤ M := by
        rw [hTdef]
        exact sigma_mul_le_one hA hε hεle hu2 hLpos hMpos hLb hMb hthr
      set σ : ℝ := 2 * T / M with hσdef
      have hσpos : 0 < σ := by rw [hσdef]; positivity
      have hσM : σ * M = 2 * T := by
        rw [hσdef]
        field_simp
      have hσL : σ * L ≤ 1 := by
        rw [hσdef, div_mul_eq_mul_div, div_le_one hMpos]
        linarith [hTL]
      have hy13 : (1 : ℝ) ≤ y ^ (1 / 3 : ℝ) := Real.one_le_rpow hy1 (by norm_num)
      have hmaj := majorant_le (Q := Q) (Q0 := y ^ (1 / 3 : ℝ)) hQ1 hy13 hσpos
      rw [← hMdef, ← hzdef, ← hLdef] at hmaj
      have hX0 : (0 : ℝ) ≤ 1 + Real.log (1 + L) := by linarith
      have hexp := exp_majorant_le (A := A) (u := Real.log x) (L := L) (M := M) (σ := σ)
        (T := T) (by linarith) hu1 hX0 hσM hσL hTdef
      have hfinal : ‖(LeanLab.KumchevLiu2007.Task129.series2 n P
            - LeanLab.KumchevLiu2007.Task129b.product2 n Q)
          - LeanLab.KumchevLiu2007.Task129b.tail2 n P (y ^ (1 / 3 : ℝ)) Q‖
          ≤ 1 / Real.log x ^ A := hstep.trans (hmaj.trans hexp)
      have hsq : ‖(LeanLab.KumchevLiu2007.Task129.series2 n P
            - LeanLab.KumchevLiu2007.Task129b.product2 n Q)
          - LeanLab.KumchevLiu2007.Task129b.tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2
          ≤ 1 / Real.log x ^ A := by
        have h1 : (1 / Real.log x ^ A) ^ 2 ≤ 1 / Real.log x ^ A := by
          have h2 : (0 : ℝ) < Real.log x := hu0
          have h3 : (0 : ℝ) < Real.log x ^ A := Real.rpow_pos_of_pos h2 A
          rw [div_pow]
          rw [div_le_div_iff₀ (by positivity) h3]
          have h4 : Real.log x ^ A * 1 ≤ Real.log x ^ A * Real.log x ^ A := by
            have h5 : (1 : ℝ) ≤ Real.log x ^ A := Real.one_le_rpow hu1 (by linarith)
            nlinarith [h5, h3]
          nlinarith [h4, h3]
        calc _ ≤ (1 / Real.log x ^ A) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hfinal 2
          _ ≤ 1 / Real.log x ^ A := h1
      exact hsq
  · -- vacuous case: `1 < ε` and `x > 1` are incompatible with `x^ε ≤ y ≤ x`
    exfalso
    push_neg at hεle
    have h2 : x < x ^ ε := by
      simpa using (Real.rpow_lt_rpow_left_iff hx1).mpr hεle
    linarith

/-- Page 14 display 50. The exact truncation_input statement follows
by summing the pointwise remainder. CONDITIONAL on the OPEN leaf. -/
theorem truncation_from_pointwise (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ intervalNumbers x y,
        ‖(series2 n P - product2 n Q) - tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2) ≤
          C * (y / Real.log x ^ A) := by
  obtain ⟨C, x0, hC, hx0, hb⟩ := smooth_remainder_pointwise A ε hA hε
  refine ⟨2 * C, x0, by positivity, hx0, ?_⟩
  intro x y P Q hx hy hyx hP hPQ hQ
  have hx2 : 2 ≤ x := hx0.trans hx
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hy1 : 1 ≤ y := (Real.one_le_rpow (by linarith : 1 ≤ x) hε.le).trans hy
  calc
    _ ≤ ∑ _n ∈ intervalNumbers x y, C / Real.log x ^ A := by
      apply Finset.sum_le_sum
      intro n hn
      exact hb x y P Q hx hy hyx hP hPQ hQ n
    _ = ((intervalNumbers x y).card : ℝ) * (C / Real.log x ^ A) := by simp
    _ ≤ (2 * y) * (C / Real.log x ^ A) := by
      exact mul_le_mul_of_nonneg_right (interval_card_le (by linarith) hy1)
        (by positivity)
    _ = (2 * C) * (y / Real.log x ^ A) := by ring

/-- Page 4 display 11. The paper's smooth indicator agrees with Mathlib's
smooth numbers at the successor of the natural floor cutoff. -/
theorem smoothWeight_eq_mathlib (q : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) :
    smoothWeight q Q = if q ∈ Nat.smoothNumbers (⌊Q⌋₊ + 1) then 1 else 0 := by
  unfold smoothWeight
  congr 1
  rw [Nat.mem_smoothNumbers']
  simp only [Nat.lt_succ_iff, Nat.le_floor_iff hQ]

end LeanLab.KumchevLiu2007.Task271a
