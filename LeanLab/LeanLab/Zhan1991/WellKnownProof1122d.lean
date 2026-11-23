/-
P0068 Zhan 1991, page 263, the "well-known approach" display before (3.1), the Prop `WellKnown`
of SPLIT_theorem2_1122. Route: drop the terms with `(n, q) > 1`, expand `e(an/q)` in Dirichlet
characters with Gauss sums, Davenport ch. 9, then bound `|τ(χ)| ≤ √q` and `φ(q)` from below.
PROVED, zero sorry: `wellKnown_proof : WellKnown`, axioms propext, Classical.choice, Quot.sound.
Ported, renamed with suffix `_wk`, since those modules are not built here: the Gauss sum bound,
the character expansion and `τ(χ₀) = μ(q)` from LeanLab.DERZ1997.Decomp1529c, unit U-1529;
Ramanujan's sum from LeanLab.PerelliPintz1992.Decomp1519; `q ≤ 4 φ(q)²` from
LeanLab.BHP1997.SPLIT_leaf_eta_cutoff561; `φ(n) ≥ log 2 · n / (1 + log n)` from
LeanLab.Pintz2021.DecompJ834. Constants: `K = 8`, `N₀ = 3`.
AI wrote the Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Zhan1991.SPLIT_theorem2_1122

namespace LeanLab.Zhan1991
open Finset Real
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

noncomputable section

/-- Gauss sum bound `|τ(χ)| ≤ √q` for every Dirichlet character mod `q`, Davenport ch. 9,
by Parseval over the twists `τ(χ, e(a·/q))`. PROVED, port of `gaussSum_norm_le` of U-1529. -/
theorem gaussSum_norm_le_wk {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ ZMod.stdAddChar‖ ≤ √q := by
  classical
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
  have hchars : (∑ x : ZMod q, χ x * star (χ x)) = (q.totient : ℂ) := by
    have ht (x : ZMod q) : χ x * star (χ x) = (1 : DirichletCharacter ℂ q) x := by
      by_cases hx : IsUnit x
      · change χ x * (starRingEnd ℂ) (χ x) = _
        rw [Complex.mul_conj', ← hx.unit_spec, χ.unit_norm_eq_one]
        simp [MulChar.one_apply hx]
      · simp [MulChar.map_nonunit _ hx]
    simp_rw [ht]
    rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  rw [hchars] at henergy
  change (∑ a : ZMod q, G a * (starRingEnd ℂ) (G a)) = _ at henergy
  simp_rw [Complex.mul_conj'] at henergy
  have hreal : (∑ a : ZMod q, ‖G a‖ ^ 2) = (q : ℝ) * q.totient := by
    exact_mod_cast henergy
  have hunit (u : (ZMod q)ˣ) : ‖G u‖ = ‖gaussSum χ e136‖ := by
    dsimp [G]
    rw [gaussSum_mulShift_eq, norm_mul, DirichletCharacter.unit_norm_eq_one, one_mul]
  have htriv : (∑ a : ZMod q, ((1 : DirichletCharacter ℂ q) a).re) = (q.totient : ℝ) := by
    have h := MulChar.sum_one_eq_card_units (R := ZMod q) (R' := ℂ)
    rw [ZMod.card_units_eq_totient] at h
    have hh := congrArg (fun z : ℂ => Complex.reCLM z) h
    rw [map_sum] at hh
    simpa using hh
  have hlow : (q.totient : ℝ) * ‖gaussSum χ e136‖ ^ 2 ≤ ∑ a : ZMod q, ‖G a‖ ^ 2 := by
    calc
      _ = ∑ a : ZMod q, ((1 : DirichletCharacter ℂ q) a).re * ‖gaussSum χ e136‖ ^ 2 := by
        rw [← Finset.sum_mul, htriv]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro a _
        by_cases ha : IsUnit a
        · rw [← ha.unit_spec, MulChar.one_apply (Units.isUnit ha.unit), Complex.one_re, one_mul,
            hunit]
        · rw [MulChar.map_nonunit _ ha, Complex.zero_re, zero_mul]
          positivity
  have hpos : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  rw [Real.le_sqrt (norm_nonneg _) (by positivity)]
  change ‖gaussSum χ e136‖ ^ 2 ≤ (q : ℝ)
  rw [hreal] at hlow
  nlinarith

/-- Port of U-1529 `stdAddChar_eq_sum_gauss`: for a unit `m` mod `q`,
`e(m/q) = (1/φ(q)) Σ_χ χ(m⁻¹) τ(χ)`, Davenport ch. 9 (1), p. 65. PROVED. -/
theorem stdAddChar_eq_sum_gauss_wk {q : ℕ} [NeZero q] {m : ZMod q} (hm : IsUnit m) :
    ZMod.stdAddChar m = (1 / (q.totient : ℂ)) *
      ∑ χ : DirichletCharacter ℂ q, χ m⁻¹ * gaussSum χ ZMod.stdAddChar := by
  unfold gaussSum
  have h_inner : ∀ χ : DirichletCharacter ℂ q,
      χ m⁻¹ * ∑ a : ZMod q, χ a * ZMod.stdAddChar a =
      ∑ a : ZMod q, χ m⁻¹ * (χ a * ZMod.stdAddChar a) := by
    intro χ
    rw [Finset.mul_sum]
  simp_rw [h_inner]
  rw [Finset.sum_comm]
  have h_sum : ∀ a : ZMod q,
      ∑ χ : DirichletCharacter ℂ q, χ m⁻¹ * (χ a * ZMod.stdAddChar a) =
      (∑ χ : DirichletCharacter ℂ q, χ m⁻¹ * χ a) * ZMod.stdAddChar a := by
    intro a
    have : (fun χ : DirichletCharacter ℂ q => χ m⁻¹ * (χ a * ZMod.stdAddChar a)) = (fun χ : DirichletCharacter ℂ q => (χ m⁻¹ * χ a) * ZMod.stdAddChar a) := by
      ext χ
      rw [mul_assoc]
    rw [this, Finset.sum_mul]
  simp_rw [h_sum]
  have h_char_sum : ∀ a : ZMod q, ∑ χ : DirichletCharacter ℂ q, χ m⁻¹ * χ a = if m = a then (q.totient : ℂ) else 0 := by
    intro a
    rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hm]
  simp_rw [h_char_sum]
  have h_eval : ∑ a : ZMod q, (if m = a then (q.totient : ℂ) else 0) * ZMod.stdAddChar a = (q.totient : ℂ) * ZMod.stdAddChar m := by
    rw [Finset.sum_eq_single m]
    · split_ifs with h_if
      · rfl
      · contradiction
    · intro b _ hb
      split_ifs with h_if
      · exact False.elim (hb h_if.symm)
      · rw [zero_mul]
    · intro h
      exfalso
      exact h (Finset.mem_univ m)
  rw [h_eval, ← mul_assoc]
  have h_div : (1 / (q.totient : ℂ)) * (q.totient : ℂ) = 1 := by
    rw [one_div, inv_mul_cancel₀]
    have h_totient_pos : 0 < q.totient := Nat.totient_pos.mpr (NeZero.pos q)
    exact_mod_cast ne_of_gt h_totient_pos
  rw [h_div, one_mul]

/-- Evaluating a character at an inverse unit is evaluating the inverse character. PROVED. -/
lemma character_inv_unit_wk {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {m : ZMod q} (hm : IsUnit m) : χ m⁻¹ = χ⁻¹ m := by
  rw [MulChar.inv_apply, ← hm.unit_spec, Ring.inverse_unit, ZMod.inv_coe_unit]

/-- Pointwise character expansion, page 263: for a unit `m` and any `n`,
`[(n, q) = 1] e(mn/q) = (1/φ(q)) Σ_χ χ̄(m) τ(χ) χ̄(n)`. PROVED. -/
lemma unit_expansion_wk {q : ℕ} [NeZero q] {m : ZMod q} (hm : IsUnit m) (n : ℕ) :
    (if IsUnit (n : ZMod q) then ZMod.stdAddChar (m * (n : ZMod q)) else 0) =
      (1 / (q.totient : ℂ)) * ∑ χ : DirichletCharacter ℂ q,
        χ⁻¹ m * gaussSum χ ZMod.stdAddChar * χ⁻¹ (n : ZMod q) := by
  by_cases hn : IsUnit (n : ZMod q)
  · rw [if_pos hn, stdAddChar_eq_sum_gauss_wk (hm.mul hn)]
    simp_rw [character_inv_unit_wk _ (hm.mul hn), map_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro χ _
    ring
  · rw [if_neg hn]
    simp [MulChar.map_nonunit _ hn]

lemma ee_add_wk (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma norm_ee_wk (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee; rw [Complex.norm_exp]; simp

lemma stdAddChar_int_mul_wk {q : ℕ} [NeZero q] (a : ℤ) (n : ℕ) :
    ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q)) = ee ((a : ℝ) * n / q) := by
  have h := ZMod.stdAddChar_coe (N := q) (a * (n : ℤ))
  simp only [Int.cast_mul, Int.cast_natCast] at h
  rw [h]
  unfold ee
  congr 1
  push_cast
  ring

/-- Ramanujan's sum at a reduced residue: `Σ_{b < q, (b,q)=1} e(ab/q) = μ(q)` for
`(a,q) = 1`; it turns the reduced residues into the main term `μ(q)/φ(q) T(η)` of `R`,
p. 357 and p. 361. Unit U-1519. -/
theorem ramanujan_coprime_wk {q a : ℕ} (hq : 1 ≤ q) (ha : Nat.Coprime a q) :
    ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q), ee ((a : ℝ) * b / q) =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  classical
  let c : ℕ → ℂ := fun n => ∑ b ∈ (Finset.range n).filter (fun b => Nat.Coprime b n), ee ((a : ℝ)*b/n)
  have hfiber : ∀ n : ℕ, 0 < n → ∀ d ∈ n.divisors,
      (∑ b ∈ (Finset.range n).filter (fun b => Nat.gcd n b = d), ee ((a : ℝ)*b/n)) = c (n/d) := by
    intro n hn d hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) hn
    obtain ⟨r, rfl⟩ := Nat.dvd_of_mem_divisors hd
    rw [Nat.mul_div_cancel_left r hd0]
    dsimp [c]
    symm
    apply Finset.sum_bij (fun b _ => d*b)
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb ⊢
      refine ⟨by nlinarith [hb.1], ?_⟩
      rw [Nat.gcd_mul_left, show Nat.gcd r b=1 from hb.2.symm, mul_one]
    · intro b hb b' hb' he
      exact Nat.eq_of_mul_eq_mul_left hd0 he
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb
      have hdb : d ∣ b := hb.2 ▸ Nat.gcd_dvd_right (d*r) b
      obtain ⟨u, rfl⟩ := hdb
      refine ⟨u, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · exact (Nat.mul_lt_mul_left hd0).mp hb.1
      · rw [Nat.gcd_mul_left] at hb
        have hg : Nat.gcd r u = 1 := by nlinarith [hb.2]
        exact (show Nat.Coprime r u from hg).symm
    · intro b hb
      have hr0 : r ≠ 0 := by intro hr; subst r; simp at hn
      push_cast
      field_simp
  have hgroup : ∀ n : ℕ, 0 < n → (∑ d ∈ n.divisors, c d) =
      ∑ b ∈ Finset.range n, ee ((a : ℝ)*b/n) := by
    intro n hn
    rw [← Nat.sum_div_divisors n c]
    calc (∑ d ∈ n.divisors, c (n/d)) = ∑ d ∈ n.divisors,
        ∑ b ∈ (Finset.range n).filter (fun b => Nat.gcd n b = d), ee ((a : ℝ)*b/n) := by
          apply Finset.sum_congr rfl
          intro d hd; exact (hfiber n hn d hd).symm
      _ = _ := Finset.sum_fiberwise_of_maps_to
        (fun b hb => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n b, by omega⟩) _
  have htotal : ∀ n : ℕ, 0 < n → n ∣ q →
      (∑ b ∈ Finset.range n, ee ((a : ℝ)*b/n)) = if n=1 then 1 else 0 := by
    intro n hn hnq
    by_cases hn1 : n=1
    · subst n; simp [ee]
    · rw [ite_eq_right hn1]
      have hac : Nat.Coprime a n := ha.of_dvd_right hnq
      have hp : IsPrimitiveRoot (ee ((a : ℝ)/n)) n := by
        convert Complex.isPrimitiveRoot_exp_of_coprime a n (by omega) hac using 1
        unfold ee; push_cast; congr 1
      have hepow : ∀ b : ℕ, ee ((a : ℝ)*b/n) = ee ((a : ℝ)/n)^b := by
        intro b
        induction b with
        | zero => simp [ee]
        | succ b ih => rw [pow_succ, ← ih, ← ee_add_wk]; congr 1; push_cast; ring
      simp_rw [hepow]
      exact hp.geom_sum_eq_zero (by omega)
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on
    (f := c) (g := fun n => if n=1 then (1 : ℂ) else 0) {n | n ∣ q}
    (fun m n hmn hn => hmn.trans hn)).mp
      (fun n hn hnq => (hgroup n hn).trans (htotal n hn hnq)) q (by omega) (dvd_refl q)
  rw [Nat.sum_divisorsAntidiagonal (fun d r => ((ArithmeticFunction.moebius d : ℤ) : ℂ) * (if r=1 then 1 else 0))] at hinv
  have hs : (∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
      (if q/d=1 then 1 else 0)) = ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
    rw [Finset.sum_eq_single q]
    · rw [Nat.div_self (by omega), ite_eq_left rfl, mul_one]
    · intro d hd hdq
      have hd' := Nat.dvd_of_mem_divisors hd
      have hneq : q/d ≠ 1 := by
        intro h
        have := Nat.div_mul_cancel hd'
        rw [h, one_mul] at this
        exact hdq this
      rw [ite_eq_right hneq, mul_zero]
    · intro h; exact False.elim (h (Nat.mem_divisors_self q (by omega)))
  rw [hs] at hinv
  exact hinv.symm

theorem gaussSum_one_wk {q : ℕ} [NeZero q] :
    gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar = (ArithmeticFunction.moebius q : ℂ) := by
  classical
  have hsum : gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar =
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ee ((1 : ℝ) * a / q) := by
    unfold gaussSum
    rw [Finset.sum_filter]
    apply Finset.sum_bij (fun a _ => a.val)
    · intro a _
      exact Finset.mem_range.mpr a.val_lt
    · intro a _ b _ h
      exact ZMod.val_injective q h
    · intro b hb
      refine ⟨(b : ZMod q), Finset.mem_univ _, ?_⟩
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hb)]
    · intro a _
      have hcop : IsUnit a ↔ Nat.Coprime a.val q := by
        rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
      by_cases ha : IsUnit a
      · rw [MulChar.one_apply ha, one_mul, if_pos (hcop.mp ha)]
        have he := ZMod.stdAddChar_coe (N := q) (a.val : ℤ)
        simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at he
        rw [he]
        unfold ee
        congr 1
        push_cast
        ring
      · rw [MulChar.map_nonunit _ ha, zero_mul, if_neg (fun h => ha (hcop.mpr h))]
  rw [hsum]
  simpa only [Nat.cast_one] using ramanujan_coprime_wk (q := q) (a := 1) (NeZero.pos q) (Nat.coprime_one_left q)

/- parity helper -/
lemma odd_of_mul_odd_wk {p m : ℕ} (h : Odd (p * m)) : Odd m := by
  rw [Nat.odd_iff] at h ⊢
  by_contra hc
  have h0 : m % 2 = 0 := by omega
  rw [Nat.mul_mod, h0, mul_zero, Nat.zero_mod] at h
  omega

/- C': p <= (p-1)^2 for p >= 3 -/
lemma prime_le_pred_sq_wk {p : ℕ} (hp : 3 ≤ p) : p ≤ (p - 1) ^ 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, p = t + 3 := ⟨p - 3, by omega⟩
  have h : t + 3 - 1 = t + 2 := by omega
  rw [h, pow_two]
  nlinarith

/- D: n <= 4 * totient n ^ 2, over the reals -/
lemma totient_key_wk (n : ℕ) :
    (n:ℝ) ≤ 4 * (n.totient:ℝ) ^ 2 ∧ (Odd n → (n:ℝ) ≤ 2 * (n.totient:ℝ) ^ 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp
    · rcases Nat.eq_or_lt_of_le hpos with h1 | h2
      · subst h1; norm_num
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
        obtain ⟨m, rfl⟩ := hpdvd
        have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.two_le
        have hp0 : (0:ℝ) ≤ (p:ℝ) := by linarith
        have hm : 0 < m := by
          rcases Nat.eq_zero_or_pos m with h | h
          · subst h; simp at h2
          · exact h
        have hlt : m < p * m := by
          have h2p := hp.two_le
          have hm1 : 0 < m := hm
          nlinarith
        obtain ⟨ihm, ihm2⟩ := ih m hlt
        have hpp : (p:ℝ) ≤ (p:ℝ)^2 := by nlinarith
        have h1p : ((p - 1 : ℕ) : ℝ) = (p:ℝ) - 1 := by
          rw [Nat.cast_sub hp.one_le]; norm_num
        constructor
        · by_cases hpm : p ∣ m
          · rw [Nat.totient_mul_of_prime_of_dvd hp hpm]; push_cast
            calc (p:ℝ) * (m:ℝ) ≤ (p:ℝ) * (4 * (m.totient:ℝ)^2) :=
                  mul_le_mul_of_nonneg_left ihm hp0
              _ = 4 * (p:ℝ) * (m.totient:ℝ)^2 := by ring
              _ ≤ 4 * (p:ℝ)^2 * (m.totient:ℝ)^2 := by
                  nlinarith [hpp, sq_nonneg (m.totient:ℝ)]
              _ = 4 * ((p:ℝ) * (m.totient:ℝ))^2 := by ring
          · rw [Nat.totient_mul_of_prime_of_not_dvd hp hpm]
            push_cast [h1p]
            rcases eq_or_lt_of_le hp.two_le with hp_eq | hp_gt
            · subst hp_eq
              norm_num
              have hmo : Odd m := by
                rw [← Nat.not_even_iff_odd, even_iff_two_dvd]; exact hpm
              have hs2 := ihm2 hmo
              calc (2:ℝ) * (m:ℝ) ≤ 2 * (2 * (m.totient:ℝ)^2) :=
                    mul_le_mul_of_nonneg_left hs2 (by norm_num)
                _ = 4 * (m.totient:ℝ)^2 := by ring
            · have hp3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp_gt
              have hsq : (p:ℝ) ≤ ((p:ℝ) - 1)^2 := by nlinarith
              calc (p:ℝ) * (m:ℝ) ≤ (p:ℝ) * (4 * (m.totient:ℝ)^2) :=
                    mul_le_mul_of_nonneg_left ihm hp0
                _ = 4 * (p:ℝ) * (m.totient:ℝ)^2 := by ring
                _ ≤ ((p:ℝ) - 1)^2 * (4 * (m.totient:ℝ)^2) := by
                    nlinarith [hsq, sq_nonneg (m.totient:ℝ)]
                _ = 4 * (((p:ℝ) - 1) * (m.totient:ℝ))^2 := by ring
        · intro hodd
          have hmo : Odd m := odd_of_mul_odd_wk hodd
          have hs2 := ihm2 hmo
          by_cases hp_eq : p = 2
          · subst hp_eq
            exact absurd hodd (by
              rw [Nat.odd_iff, Nat.mul_mod]; simp)
          · have hp3 : (3:ℝ) ≤ (p:ℝ) := by
              have : 3 ≤ p := by have := hp.two_le; omega
              exact_mod_cast this
            by_cases hpm : p ∣ m
            · rw [Nat.totient_mul_of_prime_of_dvd hp hpm]; push_cast
              calc (p:ℝ) * (m:ℝ) ≤ (p:ℝ) * (2 * (m.totient:ℝ)^2) :=
                    mul_le_mul_of_nonneg_left hs2 hp0
                _ = 2 * (p:ℝ) * (m.totient:ℝ)^2 := by ring
                _ ≤ 2 * (p:ℝ)^2 * (m.totient:ℝ)^2 := by
                    nlinarith [hpp, sq_nonneg (m.totient:ℝ)]
                _ = 2 * ((p:ℝ) * (m.totient:ℝ))^2 := by ring
            · rw [Nat.totient_mul_of_prime_of_not_dvd hp hpm]
              push_cast [h1p]
              have hsq : (p:ℝ) ≤ ((p:ℝ) - 1)^2 := by nlinarith
              calc (p:ℝ) * (m:ℝ) ≤ (p:ℝ) * (2 * (m.totient:ℝ)^2) :=
                    mul_le_mul_of_nonneg_left hs2 hp0
                _ = 2 * (p:ℝ) * (m.totient:ℝ)^2 := by ring
                _ ≤ ((p:ℝ) - 1)^2 * (2 * (m.totient:ℝ)^2) := by
                    nlinarith [hsq, sq_nonneg (m.totient:ℝ)]
                _ = 2 * (((p:ℝ) - 1) * (m.totient:ℝ))^2 := by ring

lemma totient_sq_ge_wk (n : ℕ) : (n:ℝ) ≤ 4 * (n.totient:ℝ) ^ 2 := (totient_key_wk n).1

/-- The product bound: `∏ p ≤ (|s| + 1) ∏ (p - 1)`, i.e. `∏ p/(p - 1) ≤ |s| + 1`. Induction on the maximum element:
removing `a` leaves `|s| - 1` elements, all `≥ 2` and `< a`, so `a ≥ |s| + 1`, and `a ≥ |s| + 1` is
exactly what `a·|s| ≤ (|s| + 1)(a - 1)` needs. -/
theorem prod_le_card_succ_mul_prod_pred_wk {s : Finset ℕ} (h2 : ∀ p ∈ s, 2 ≤ p) :
    ∏ p ∈ s, p ≤ (s.card + 1) * ∏ p ∈ s, (p - 1) := by
  revert h2
  refine Finset.induction_on_max s ?_ ?_
  · intro _
    simp
  · intro a s ha ih h2
    have h2a : 2 ≤ a := h2 a (Finset.mem_insert_self a s)
    have h2s : ∀ p ∈ s, 2 ≤ p := fun p hp => h2 p (Finset.mem_insert_of_mem hp)
    have han : a ∉ s := fun h => absurd (ha a h) (lt_irrefl a)
    have hP := ih h2s
    have hsub : s ⊆ Finset.Icc 2 (a - 1) := by
      intro x hx
      rw [Finset.mem_Icc]
      exact ⟨h2s x hx, by have := ha x hx; omega⟩
    have hcard : s.card ≤ a - 2 := by
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc] at this
      omega
    have ham : s.card + 2 ≤ a := by omega
    obtain ⟨t, ht⟩ : ∃ t, a = s.card + 2 + t := ⟨a - (s.card + 2), by omega⟩
    have ha1 : a - 1 = s.card + 1 + t := by omega
    rw [Finset.prod_insert han, Finset.prod_insert han, Finset.card_insert_of_notMem han, ha1, ht]
    calc (s.card + 2 + t) * ∏ p ∈ s, p
        ≤ (s.card + 2 + t) * ((s.card + 1) * ∏ p ∈ s, (p - 1)) :=
          Nat.mul_le_mul_left _ hP
      _ = ((s.card + 2 + t) * (s.card + 1)) * ∏ p ∈ s, (p - 1) := by ring
      _ ≤ ((s.card + 1 + 1) * (s.card + 1 + t)) * ∏ p ∈ s, (p - 1) := by
          refine Nat.mul_le_mul_right _ ?_
          nlinarith
      _ = (s.card + 1 + 1) * ((s.card + 1 + t) * ∏ p ∈ s, (p - 1)) := by ring

/-- `n ≤ φ(n) * (number of distinct prime divisors of n + 1)`. -/
theorem totient_mul_card_succ_ge_wk (n : ℕ) :
    n ≤ Nat.totient n * (n.primeFactors.card + 1) := by
  have hid := Nat.totient_mul_prod_primeFactors n
  have hP : ∏ p ∈ n.primeFactors, p ≤
      (n.primeFactors.card + 1) * ∏ p ∈ n.primeFactors, (p - 1) :=
    prod_le_card_succ_mul_prod_pred_wk fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).two_le
  have hQ : 0 < ∏ p ∈ n.primeFactors, (p - 1) := by
    refine Finset.prod_pos fun p hp => ?_
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have hmain : n * ∏ p ∈ n.primeFactors, (p - 1) ≤
      (Nat.totient n * (n.primeFactors.card + 1)) * ∏ p ∈ n.primeFactors, (p - 1) := by
    calc n * ∏ p ∈ n.primeFactors, (p - 1)
        = Nat.totient n * ∏ p ∈ n.primeFactors, p := hid.symm
      _ ≤ Nat.totient n * ((n.primeFactors.card + 1) *
            ∏ p ∈ n.primeFactors, (p - 1)) := Nat.mul_le_mul_left _ hP
      _ = (Nat.totient n * (n.primeFactors.card + 1)) *
            ∏ p ∈ n.primeFactors, (p - 1) := by ring
  exact Nat.le_of_mul_le_mul_right hmain hQ

theorem totient_ge_div_card_succ_wk (n : ℕ) :
    (n : ℝ) / ((n.primeFactors.card : ℝ) + 1) ≤ (Nat.totient n : ℝ) := by
  have h := totient_mul_card_succ_ge_wk n
  have hc : (0 : ℝ) < (n.primeFactors.card : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hc]
  have h' : (n : ℝ) ≤ (Nat.totient n : ℝ) * ((n.primeFactors.card : ℝ) + 1) := by
    exact_mod_cast h
  linarith

theorem two_pow_card_primeFactors_le_wk {n : ℕ} (hn : 1 ≤ n) :
    2 ^ n.primeFactors.card ≤ n := by
  have key : ∀ s : Finset ℕ, (∀ p ∈ s, 2 ≤ p) → 2 ^ s.card ≤ ∏ p ∈ s, p := by
    intro s
    induction s using Finset.induction with
    | empty => intro _; simp
    | insert a s ha ih =>
        intro hs
        have h2a : 2 ≤ a := hs a (Finset.mem_insert_self a s)
        have h2s : ∀ p ∈ s, 2 ≤ p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
        rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ]
        calc 2 ^ s.card * 2 ≤ (∏ p ∈ s, p) * a := Nat.mul_le_mul (ih h2s) h2a
          _ = a * ∏ p ∈ s, p := by ring
  have h1 : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
    key _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hpos : 0 < n := by omega
  exact h1.trans (Nat.le_of_dvd hpos (Nat.prod_primeFactors_dvd n))

theorem card_primeFactors_le_log_div_wk {n : ℕ} (hn : 1 ≤ n) :
    (n.primeFactors.card : ℝ) ≤ Real.log n / Real.log 2 := by
  have h2 := two_pow_card_primeFactors_le_wk hn
  have h2' : (2 : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) := by exact_mod_cast h2
  have hbase : (0 : ℝ) < (2 : ℝ) ^ n.primeFactors.card := by positivity
  have hlog := Real.log_le_log hbase h2'
  rw [Real.log_pow] at hlog
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog2]
  linarith

/-- **`φ(n) ≫ n / log n`**: `log 2 · n / (1 + log n) ≤ φ(n)` for `n ≥ 1`, the shape the coefficient
bound `‖c'‖ ≪ q^{-3/2} (1 + log q)^2` needs. -/
theorem totient_ge_log_two_mul_div_wk {n : ℕ} (hn : 1 ≤ n) :
    Real.log 2 * (n : ℝ) / (1 + Real.log n) ≤ (Nat.totient n : ℝ) := by
  have hφ := totient_ge_div_card_succ_wk n
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    linarith
  have hlog1 : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hk := card_primeFactors_le_log_div_wk hn
  -- `k + 1 ≤ (1 + log n) / log 2`
  have hk2 : (n.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [le_div_iff₀ hlog2] at hk
    linarith
  have hk1 : ((n.primeFactors.card : ℝ) + 1) * Real.log 2 ≤ 1 + Real.log n := by
    nlinarith [hk2, hlog2lt]
  have hone : (0 : ℝ) < (n.primeFactors.card : ℝ) + 1 := by positivity
  -- `log 2 · n / (1 + log n) ≤ n / (k + 1)`
  have hstep : Real.log 2 * (n : ℝ) / (1 + Real.log n) ≤
      (n : ℝ) / ((n.primeFactors.card : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 1 + Real.log n) hone]
    nlinarith [hk1, hnpos, hlog2]
  exact hstep.trans hφ
/-- Page 263, the principal character term: `|τ(χ₀)| = |c_q(1)| = |μ(q)| ≤ 1`, Hardy-Wright
Theorem 271, Davenport ch. 26 p. 147. PROVED. -/
theorem gaussSum_one_norm_le_wk {q : ℕ} [NeZero q] :
    ‖gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar‖ ≤ 1 := by
  rw [gaussSum_one_wk, Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- Page 263, `φ(q) ≫ q^{1/2}`: `√q ≤ 2 φ(q)`, from `q ≤ 4 φ(q)²`. PROVED. -/
theorem sqrt_le_two_totient_wk (q : ℕ) (_hq : 1 ≤ q) :
    Real.sqrt q ≤ 2 * (q.totient : ℝ) := by
  calc Real.sqrt q ≤ Real.sqrt ((2 * (q.totient : ℝ)) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [totient_sq_ge_wk q])
    _ = 2 * (q.totient : ℝ) := Real.sqrt_sq (by positivity)

/-- Page 263, `φ(q) ≫ q L⁻¹`: from `φ(q)/q ≥ 1/(ω(q)+1)` and `ω(q) ≤ log q / log 2`. PROVED. -/
theorem le_log_mul_totient_wk (q : ℕ) (hq : 1 ≤ q) :
    (q : ℝ) ≤ 2 * (Real.log q + 1) * (q.totient : ℝ) := by
  have h := totient_ge_log_two_mul_div_wk hq
  have hl : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  rw [div_le_iff₀ (by linarith)] at h
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  nlinarith [mul_le_mul_of_nonneg_right hlog2.le hq0]

/-- Page 263: the mass of one prime `p` on `n ≤ N`, `p ∣ n`, is `Σ Λ(n) ≤ log N`, since only
the powers `p^k ≤ N` count, each with `Λ = log p`. PROVED. -/
lemma prime_mass_le_wk (N p : ℕ) (hp : p.Prime) (hN : 1 ≤ N) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => p ∣ n), Λ n ≤ Real.log N := by
  classical
  set S := (Finset.Icc 1 N).filter (fun n => p ∣ n)
  set K := Nat.log p N
  have hsub : S.filter (fun n => Λ n ≠ 0) ⊆ (Finset.Icc 1 K).image (fun k => p ^ k) := by
    intro n hn
    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨⟨hn1, hnN⟩, hpn⟩, hΛ⟩ := hn
    rw [ArithmeticFunction.vonMangoldt_ne_zero_iff, isPrimePow_nat_iff] at hΛ
    obtain ⟨r, k, hr, hk, rfl⟩ := hΛ
    have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hpn)
    subst hpr
    simp only [Finset.mem_image, Finset.mem_Icc]
    exact ⟨k, ⟨hk, Nat.le_log_of_pow_le hp.one_lt hnN⟩, rfl⟩
  have hval : ∀ n ∈ S.filter (fun n => Λ n ≠ 0), Λ n = Real.log p := by
    intro n hn
    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨⟨hn1, hnN⟩, hpn⟩, hΛ⟩ := hn
    rw [ArithmeticFunction.vonMangoldt_ne_zero_iff, isPrimePow_nat_iff] at hΛ
    obtain ⟨r, k, hr, hk, rfl⟩ := hΛ
    have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hpn)
    subst hpr
    rw [ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hcard : (S.filter (fun n => Λ n ≠ 0)).card ≤ K := by
    calc _ ≤ ((Finset.Icc 1 K).image (fun k => p ^ k)).card := Finset.card_le_card hsub
      _ ≤ (Finset.Icc 1 K).card := Finset.card_image_le
      _ = K := by simp
  have hlogp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hp0 := hp.pos
  calc ∑ n ∈ S, Λ n = ∑ n ∈ S.filter (fun n => Λ n ≠ 0), Λ n :=
        (Finset.sum_filter_ne_zero _).symm
    _ = (S.filter (fun n => Λ n ≠ 0)).card * Real.log p := by
        rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
    _ ≤ K * Real.log p := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hlogp
    _ = Real.log ((p ^ K : ℕ) : ℝ) := by push_cast; rw [Real.log_pow]
    _ ≤ Real.log N := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast Nat.pow_log_le_self p (by omega)

/-- Page 263, "drop `(n, q) > 1` at cost `O(L²)`": the `n ≤ N` with `Λ(n) ≠ 0` and
`(n, q) > 1` are powers of the at most `log q / log 2` primes `p ∣ q`, each `p` giving mass
`≤ log N`. PROVED. -/
theorem noncoprime_mass_wk (N q : ℕ) (hN : 2 ≤ N) (hq : 1 ≤ q) (hqN : q ≤ N) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Coprime n q), Λ n ≤
      2 * Real.log N ^ 2 := by
  classical
  have hnn : ∀ (n p : ℕ), 0 ≤ (if p ∣ n then Λ n else 0) := by
    intro n p; split_ifs
    · exact ArithmeticFunction.vonMangoldt_nonneg
    · exact le_refl _
  have hpt : ∀ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Coprime n q),
      Λ n ≤ ∑ p ∈ q.primeFactors, (if p ∣ n then Λ n else 0) := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    obtain ⟨p, hp, hpn, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn.2
    have hpmem : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpq, by omega⟩
    calc Λ n = (if p ∣ n then Λ n else 0) := by rw [if_pos hpn]
      _ ≤ _ := Finset.single_le_sum (f := fun p => if p ∣ n then Λ n else 0)
          (fun i _ => hnn n i) hpmem
  calc _ ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Coprime n q),
        ∑ p ∈ q.primeFactors, (if p ∣ n then Λ n else 0) := Finset.sum_le_sum hpt
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ q.primeFactors, (if p ∣ n then Λ n else 0) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro i _ _
        exact Finset.sum_nonneg (fun p _ => hnn i p)
    _ = ∑ p ∈ q.primeFactors, ∑ n ∈ (Finset.Icc 1 N).filter (fun n => p ∣ n), Λ n := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.sum_filter]
    _ ≤ ∑ p ∈ q.primeFactors, Real.log N := by
        apply Finset.sum_le_sum
        intro p hp
        exact prime_mass_le_wk N p (Nat.prime_of_mem_primeFactors hp) (by omega)
    _ = q.primeFactors.card * Real.log N := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * Real.log N ^ 2 := by
        have hc := card_primeFactors_le_log_div_wk hq
        have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
        have hlq : Real.log q ≤ Real.log N :=
          Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast hqN)
        have hL0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
        have hc0 : (0 : ℝ) ≤ q.primeFactors.card := Nat.cast_nonneg _
        have hc2 : (q.primeFactors.card : ℝ) ≤ 2 * Real.log N := by
          rw [le_div_iff₀ (by linarith)] at hc
          nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hc2 hL0]

lemma card_shortWin_wk (N : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    ((shortWin N A).card : ℝ) ≤ A + 1 := by
  have hsub : shortWin N A ⊆ Finset.Icc (N - ⌊A⌋₊) N := by
    intro n hn
    simp only [shortWin, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    refine ⟨?_, hn.1.2⟩
    have h1 := Nat.lt_floor_add_one A
    have h2 : (N : ℝ) < n + (⌊A⌋₊ + 1) := by linarith [hn.2]
    have h3 : N < n + (⌊A⌋₊ + 1) := by exact_mod_cast h2
    omega
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  have hc2 : (shortWin N A).card ≤ ⌊A⌋₊ + 1 := by omega
  have : ((shortWin N A).card : ℝ) ≤ ⌊A⌋₊ + 1 := by exact_mod_cast hc2
  linarith [Nat.floor_le hA]

lemma norm_Schi_le_wk {q : ℕ} (χ : DirichletCharacter ℂ q) (lam : ℝ) (N : ℕ) (A : ℝ)
    (hA : 0 ≤ A) : ‖Schi χ lam N A‖ ≤ (A + 1) * Real.log N := by
  unfold Schi
  calc ‖∑ n ∈ shortWin N A, (Λ n : ℂ) * χ n * ee (n * lam)‖
      ≤ ∑ n ∈ shortWin N A, ‖(Λ n : ℂ) * χ n * ee (n * lam)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ shortWin N A, Real.log N := by
        apply Finset.sum_le_sum
        intro n hn
        simp only [shortWin, Finset.mem_filter, Finset.mem_Icc] at hn
        rw [norm_mul, norm_mul, norm_ee_wk, mul_one, Complex.norm_real,
          Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        calc Λ n * ‖χ n‖ ≤ Λ n * 1 :=
              mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one _ _)
                ArithmeticFunction.vonMangoldt_nonneg
          _ ≤ Real.log n := by rw [mul_one]; exact ArithmeticFunction.vonMangoldt_le_log
          _ ≤ Real.log N := by
              apply Real.log_le_log (by exact_mod_cast hn.1.1) (by exact_mod_cast hn.1.2)
    _ = (shortWin N A).card * Real.log N := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (A + 1) * Real.log N := by
        apply mul_le_mul_of_nonneg_right (card_shortWin_wk N A hA)
        exact Real.log_natCast_nonneg N

/-- The character sum after expansion, split at `χ₀`, with `|τ(χ)| ≤ √q`. PROVED. -/
lemma char_part_bound_wk {q : ℕ} [NeZero q] (m : ZMod q) (S : DirichletCharacter ℂ q → ℂ) :
    ‖(1 / (q.totient : ℂ)) * ∑ χ : DirichletCharacter ℂ q,
        χ⁻¹ m * gaussSum χ ZMod.stdAddChar * S χ⁻¹‖ ≤
      (1 / (q.totient : ℝ)) * (‖S 1‖ +
        Real.sqrt q * ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ‖S χ‖) := by
  classical
  have hnorm : ‖(1 / (q.totient : ℂ))‖ = 1 / (q.totient : ℝ) := by
    simp [norm_div, Complex.norm_natCast]
  rw [norm_mul, hnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  let g : DirichletCharacter ℂ q → ℝ := fun χ => ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ * ‖S χ‖
  calc ‖∑ χ : DirichletCharacter ℂ q, χ⁻¹ m * gaussSum χ ZMod.stdAddChar * S χ⁻¹‖
      ≤ ∑ χ : DirichletCharacter ℂ q, ‖χ⁻¹ m * gaussSum χ ZMod.stdAddChar * S χ⁻¹‖ :=
        norm_sum_le _ _
    _ ≤ ∑ χ : DirichletCharacter ℂ q, g χ⁻¹ := by
        apply Finset.sum_le_sum
        intro χ _
        simp only [g, inv_inv]
        rw [norm_mul, norm_mul]
        have := DirichletCharacter.norm_le_one χ⁻¹ m
        have h0 : 0 ≤ ‖gaussSum χ ZMod.stdAddChar‖ * ‖S χ⁻¹‖ := by positivity
        nlinarith [norm_nonneg (gaussSum χ ZMod.stdAddChar), norm_nonneg (S χ⁻¹)]
    _ = ∑ χ : DirichletCharacter ℂ q, g χ :=
        Fintype.sum_equiv (Equiv.inv _) (fun χ => g χ⁻¹) g (fun _ => rfl)
    _ = g 1 + ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1), g χ := by
        rw [Finset.filter_ne', Finset.add_sum_erase _ _ (Finset.mem_univ _)]
    _ ≤ ‖S 1‖ + ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          Real.sqrt q * ‖S χ‖ := by
        apply add_le_add
        · simp only [g, inv_one]
          have := gaussSum_one_norm_le_wk (q := q)
          nlinarith [norm_nonneg (S 1)]
        · apply Finset.sum_le_sum
          intro χ _
          exact mul_le_mul_of_nonneg_right (gaussSum_norm_le_wk χ⁻¹) (norm_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

theorem wellKnown_proof : WellKnown := by
  classical
  refine ⟨8, 3, ?_⟩
  intro N A α lam a q _ hN hA1 hAN hα hgcd hqN
  set L := Real.log N with hL
  have hN3 : (3 : ℝ) ≤ N := hN
  have hN2 : 2 ≤ N := by exact_mod_cast (by linarith : (2 : ℝ) ≤ N)
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hq1n : 1 ≤ q := NeZero.one_le
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq1n
  have hqpos : (0 : ℝ) < q := by linarith
  set m : ZMod q := (a : ZMod q) with hmdef
  have hm : IsUnit m := by
    have h := Int.gcd_eq_gcd_ab a q
    rw [hgcd] at h
    refine isUnit_iff_exists_inv.mpr ⟨((Int.gcdA a q : ℤ) : ZMod q), ?_⟩
    have h2 := congrArg (fun z : ℤ => (z : ZMod q)) h
    simp only [Nat.cast_one, Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_self, zero_mul, add_zero] at h2
    exact h2.symm
  -- split each term
  set W := shortWin N A
  have hterm : ∀ n : ℕ, (Λ n : ℂ) * ee (n * α) =
      (Λ n : ℂ) * ee (n * lam) * (if IsUnit (n : ZMod q) then
        ZMod.stdAddChar (m * (n : ZMod q)) else 0) +
      (Λ n : ℂ) * ee (n * lam) * (if IsUnit (n : ZMod q) then 0 else
        ZMod.stdAddChar (m * (n : ZMod q))) := by
    intro n
    have he : ee (n * α) = ee ((a : ℝ) * n / q) * ee (n * lam) := by
      rw [← ee_add_wk, hα]; congr 1; ring
    rw [he, ← stdAddChar_int_mul_wk]
    split_ifs <;> ring
  have hsplit : Sexp α N A =
      (1 / (q.totient : ℂ)) * ∑ χ : DirichletCharacter ℂ q,
        χ⁻¹ m * gaussSum χ ZMod.stdAddChar * Schi χ⁻¹ lam N A +
      ∑ n ∈ W, (Λ n : ℂ) * ee (n * lam) * (if IsUnit (n : ZMod q) then 0 else
        ZMod.stdAddChar (m * (n : ZMod q))) := by
    unfold Sexp
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    congr 1
    simp_rw [unit_expansion_wk hm]
    unfold Schi
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro χ _
    ring
  -- bound the non-coprime part
  have hT2 : ‖∑ n ∈ W, (Λ n : ℂ) * ee (n * lam) * (if IsUnit (n : ZMod q) then 0 else
        ZMod.stdAddChar (m * (n : ZMod q)))‖ ≤ 2 * L ^ 2 := by
    calc _ ≤ ∑ n ∈ W, ‖(Λ n : ℂ) * ee (n * lam) * (if IsUnit (n : ZMod q) then 0 else
          ZMod.stdAddChar (m * (n : ZMod q)))‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ W, (if Nat.Coprime n q then 0 else Λ n) := by
          apply Finset.sum_le_sum
          intro n _
          have hu := ZMod.isUnit_iff_coprime n q
          by_cases h : Nat.Coprime n q
          · rw [if_pos h, if_pos (hu.mpr h)]; simp
          · rw [if_neg h, if_neg (fun h' => h (hu.mp h'))]
            rw [norm_mul, norm_mul, norm_ee_wk, mul_one, Complex.norm_real,
              Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
            simp [AddChar.norm_apply]
      _ ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Coprime n q), Λ n := by
          rw [Finset.sum_filter]
          simp_rw [ite_not]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            simp only [W, shortWin, Finset.mem_filter] at hn
            exact hn.1
          · intro n _ _
            split_ifs
            · exact le_refl _
            · exact ArithmeticFunction.vonMangoldt_nonneg
      _ ≤ 2 * L ^ 2 := noncoprime_mass_wk N q hN2 hq1n (by exact_mod_cast hqN)
  have hchar := char_part_bound_wk m (fun χ => Schi χ lam N A)
  have hP := norm_Schi_le_wk (1 : DirichletCharacter ℂ q) lam N A (by linarith)
  set T := ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
    ‖Schi χ lam N A‖ with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hphi : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  set s := Real.sqrt q with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hqpos
  have hss : s * s = q := Real.mul_self_sqrt hqpos.le
  have h1 : s ≤ 2 * q.totient := sqrt_le_two_totient_wk q hq1n
  have h2 : (q : ℝ) ≤ 2 * (Real.log q + 1) * q.totient := le_log_mul_totient_wk q hq1n
  have hlogq : Real.log q ≤ L := Real.log_le_log hqpos hqN
  have h2' : s * s ≤ 4 * L * q.totient := by rw [hss]; nlinarith
  have hrp : (q : ℝ) ^ (-(1 / 2) : ℝ) = 1 / s := by
    rw [Real.rpow_neg hqpos.le, ← Real.sqrt_eq_rpow, one_div]
  have hL2 : L ^ (2 : ℝ) = L ^ 2 := Real.rpow_two L
  have hu1 : 1 / (q.totient : ℝ) ≤ 2 / s := by
    rw [div_le_div_iff₀ hphi hs0]; linarith
  have hu2 : 1 / (q.totient : ℝ) * s ≤ 4 * L / s := by
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hphi hs0]; linarith
  have hL0 : 0 ≤ L := by linarith
  have ht0 : 0 ≤ 1 / s := by positivity
  rw [hrp, hL2, hsplit]
  calc _ ≤ ‖(1 / (q.totient : ℂ)) * ∑ χ : DirichletCharacter ℂ q,
        χ⁻¹ m * gaussSum χ ZMod.stdAddChar * Schi χ⁻¹ lam N A‖ +
      ‖∑ n ∈ W, (Λ n : ℂ) * ee (n * lam) * (if IsUnit (n : ZMod q) then 0 else
        ZMod.stdAddChar (m * (n : ZMod q)))‖ := norm_add_le _ _
    _ ≤ (1 / (q.totient : ℝ)) * (‖Schi 1 lam N A‖ + s * T) + 2 * L ^ 2 :=
        add_le_add hchar hT2
    _ = 1 / (q.totient : ℝ) * ‖Schi 1 lam N A‖ + (1 / (q.totient : ℝ) * s) * T + 2 * L ^ 2 := by
        ring
    _ ≤ 2 / s * ((A + 1) * L) + 4 * L / s * T + 2 * L ^ 2 := by
        gcongr
    _ = 2 * (1 / s) * ((A + 1) * L) + 4 * L * (1 / s) * T + 2 * L ^ 2 := by ring
    _ ≤ 8 * (L * (1 / s) * T + L ^ 2 + L * A * (1 / s)) := by
        nlinarith [mul_nonneg (mul_nonneg hL0 ht0) hT0,
          mul_nonneg (mul_nonneg hL0 ht0) (by linarith : (0 : ℝ) ≤ A - 1), sq_nonneg L]
