import LeanLab.ExceptionalSet.UpJ200.Lemma2MV.Lemma55Split

/-!
# Split of the leaf `lem55_termwise`, P0015 display (5.5) termwise, pages 358 to 360

Source P0015, Montgomery and Vaughan, The exceptional set in Goldbach's problem,
Acta Arith. 27, 1975, read from the page images of `papers/P0015.pdf`, PDF pages 4 and 5,
journal pages 358 to 360.

The termwise bound behind display (5.5) rests on Lemmas 5.1, 5.2, 5.3 and 5.4 of Section 5,
stated for the lab's `rem66_cchi`, where `τ(χ) = c_χ(1)`, and for `changeLevel` characters.
* `mv_lemma51_norm_le`, PROVED: the upper half of Lemma 5.1, page 358, `|τ(χ)| ≤ q^{1/2}`,
  through `rem66_cchi_one_eq_gaussSum` and Mathlib's `gaussSum`.
* `mv_lemma52`, PROVED: Lemma 5.2, page 358, `τ(χ) = μ(k/r) χ*(k/r) τ(χ*)`, by
  `Σ_{d | (h,k)} μ(d) = [(h,k) = 1]` and `Σ_{j < rs} ψ(j) e(j/rs) = 0` for `s > 1`.
* `mv_lemma53_shift`, PROVED: the one line proof of Lemma 5.3, page 358,
  `χ(m) c_χ(m) = c_χ(1)` for `(m, k) = 1`; `mv_lemma53`, Lemma 5.3, PROVED from it and 5.2.
* `mv_lemma54_case1` and `mv_lemma54_case2`, PROVED: the two cases of the
  proof of Lemma 5.4, pages 359 and 360; `mv_lemma54_of`, Lemma 5.4 display (5.1), PROVED from
  them and Lemma 5.3.
* PROVED: the arithmetic of page 360, `(k, r₄) = 1` and `μ(k)² = 1` for a non-zero term,
  `φ(q) = φ(r₄)φ(k)`, `q/(q,m) = (r₄/r₅)(k/(k,m))` with coprime factors, and `r₃ | r₄/r₅`.
* `lem55_termwise_of_leaves`, PROVED sorry free with Lemma 5.2 as a hypothesis, and
  `lem55_termwise_split`, PROVED sorry free outright: the exact statement of `lem55_termwise`,
  with the absolute constant `C = 1`; twin `lem55_termwise_split_twin`. No LEAF remains.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit

open Real Finset DirichletCharacter
open LeanLab.ExceptionalSet.U1539 (eC)

/-! ### Lemmas 5.1 to 5.4 of Section 5 -/

/-- P0015 display (2.1): the lab's `c_χ(m) = rem66_cchi χ m` is Mathlib's Gauss sum
`gaussSum χ (ZMod.stdAddChar.mulShift m)`, PROVED. -/
theorem rem66_cchi_eq_gaussSum_mulShift {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (m : ℤ) : rem66_cchi χ m = gaussSum χ (ZMod.stdAddChar.mulShift (m : ZMod q)) := by
  unfold rem66_cchi gaussSum
  symm
  refine Finset.sum_nbij' (fun a : ZMod q => a.val) (fun h => (h : ZMod q)) ?_ ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro h _; exact Finset.mem_univ _
  · intro a _; exact ZMod.natCast_zmod_val a
  · intro h hh; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hh)
  · intro a _
    have e : (ZMod.stdAddChar.mulShift (m : ZMod q)) a =
        Complex.exp (2 * π * Complex.I * (((m * a.val : ℤ)) : ℂ) / q) := by
      rw [AddChar.mulShift_apply, ← ZMod.stdAddChar_coe]
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [e, ZMod.natCast_zmod_val]
    congr 1
    unfold eC
    congr 1
    push_cast
    ring

/-- P0015 display (2.1) at `m = 1`: `τ(χ) = c_χ(1) = rem66_cchi χ 1` is Mathlib's
`gaussSum χ ZMod.stdAddChar`, PROVED. -/
theorem rem66_cchi_one_eq_gaussSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    rem66_cchi χ 1 = gaussSum χ ZMod.stdAddChar := by
  rw [rem66_cchi_eq_gaussSum_mulShift, Int.cast_one, AddChar.mulShift_one]

/-- P0015 Lemma 5.1, first sentence, page 358, the upper half, PROVED: `|τ(χ)| ≤ q^{1/2}` for
every character `χ` mod `q`; for primitive `χ` Lemma 5.1 gives equality, and only this upper
bound is used on page 360. The proof is the energy identity `Σ_a |τ(χ, e_a)|² = q φ(q)`,
copied from the lab's `DERZ1997.Decomp1529c.gaussSum_norm_le`, a Mathlib only proof. -/
theorem mv_lemma51_norm_le : ∀ (r : ℕ) (ψ : DirichletCharacter ℂ r), 1 ≤ r →
    ‖rem66_cchi ψ 1‖ ≤ Real.sqrt r := by
  classical
  intro q χ hq1
  have : NeZero q := ⟨by omega⟩
  rw [rem66_cchi_one_eq_gaussSum]
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

/-- Splitting `j < r s` as `j = r i + j₀`, used for Lemma 5.2 of P0015, page 358, PROVED. -/
theorem mv52_block (r : ℕ) (F : ℕ → ℂ) : ∀ s : ℕ,
    ∑ j ∈ range (r * s), F j = ∑ i ∈ range s, ∑ j ∈ range r, F (r * i + j) := by
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

/-- For `ψ` mod `r` and `s > 1`, `Σ_{j < rs} ψ(j) e(j/(rs)) = 0`, since `Σ_{i<s} e(i/s) = 0`;
used for Lemma 5.2 of P0015, page 358, PROVED. -/
theorem mv52_vanish {r : ℕ} (ψ : DirichletCharacter ℂ r) (s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hs1 : s ≠ 1) :
    ∑ j ∈ range (r * s), ψ (j : ZMod r) * eC ((j : ℝ) / (r * s : ℕ)) = 0 := by
  rw [mv52_block r _ s]
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
  have e : ∀ i j : ℕ, ψ ((r * i + j : ℕ) : ZMod r) * eC (((r * i + j : ℕ) : ℝ) / (r * s : ℕ)) =
      (ψ (j : ZMod r) * eC ((j : ℝ) / (r * s : ℕ))) * eC ((i : ℝ) / s) := by
    intro i j
    have h1 : ((r * i + j : ℕ) : ZMod r) = (j : ZMod r) := by
      push_cast; rw [ZMod.natCast_self, zero_mul, zero_add]
    have h2 : ((r * i + j : ℕ) : ℝ) / (r * s : ℕ) = (j : ℝ) / (r * s : ℕ) + (i : ℝ) / s := by
      push_cast; field_simp; ring
    rw [h1, h2, rem66_eC_add]; ring
  simp_rw [e]
  rw [sum_comm]
  simp_rw [← mul_sum]
  rw [rem66_geom s hs, ite_eq_right_of_eq_false _ _ (eq_false hs1)]
  simp

/-- P0015 Lemma 5.2, page 358, cited there from Davenport p. 148, PROVED. Let `χ` be
a character mod `k` induced by the primitive character `χ*` mod `r`, so `r | k`; then
`τ(χ) = μ(k/r) χ*(k/r) τ(χ*)`. Here `χ = changeLevel h χ*`. -/
theorem mv_lemma52 : ∀ (r k : ℕ) (ψ : DirichletCharacter ℂ r) (h : r ∣ k), 1 ≤ k →
    ψ.IsPrimitive →
    rem66_cchi (changeLevel h ψ) 1 =
      ((ArithmeticFunction.moebius (k / r) : ℤ) : ℂ) * ψ ((k / r : ℕ) : ZMod r) *
        rem66_cchi ψ 1 := by
  intro r k ψ h hk _
  have : NeZero k := ⟨by omega⟩
  have hr : 1 ≤ r := Nat.pos_of_ne_zero (by rintro rfl; simp at h; omega)
  unfold rem66_cchi
  -- step 1: insert Σ_{d | (h,k)} μ(d)
  have h1 : ∀ x ∈ range k, (changeLevel h ψ) (x : ZMod k) * eC ((x : ℝ) * ((1 : ℤ) : ℝ) / k) =
      ∑ d ∈ (Nat.gcd x k).divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        (ψ (x : ZMod r) * eC ((x : ℝ) / k)) := by
    intro x _
    rw [← sum_mul, rem66_sum_moebius]
    have e : eC ((x : ℝ) * ((1 : ℤ) : ℝ) / k) = eC ((x : ℝ) / k) := by push_cast; rw [mul_one]
    rw [e]
    by_cases hc : Nat.Coprime x k
    · have hc' : Nat.gcd x k = 1 := hc
      have hic : IsCoprime (x : ℤ) (k : ℤ) := Nat.isCoprime_iff_coprime.mpr hc
      have := changeLevel_eq_cast_of_dvd' ψ h hic
      push_cast at this
      rw [this]
      simp [hc']
    · rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])]
      have hc' : Nat.gcd x k ≠ 1 := hc
      simp [hc']
  rw [sum_congr rfl h1]
  rw [Finset.sum_comm' (t' := k.divisors) (s' := fun d => (range k).filter (fun x => d ∣ x))]
  swap
  · intro x d
    simp only [mem_range, Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
    have hg : Nat.gcd x k ≠ 0 := (Nat.gcd_pos_of_pos_right x (by omega)).ne'
    constructor
    · rintro ⟨hh, ⟨hdh, hdq⟩, _⟩; exact ⟨⟨hh, hdh⟩, hdq, by omega⟩
    · rintro ⟨⟨hh, hdh⟩, hdq, _⟩; exact ⟨hh, ⟨hdh, hdq⟩, hg⟩
  simp_rw [← mul_sum]
  -- step 3: the inner sums
  have h3 : ∀ d ∈ k.divisors, ∑ x ∈ (range k).filter (fun x => d ∣ x),
      ψ (x : ZMod r) * eC ((x : ℝ) / k) =
      ψ (d : ZMod r) * ∑ j ∈ range (k / d), ψ (j : ZMod r) * eC ((j : ℝ) / (k / d : ℕ)) := by
    intro d hd
    have hdk : d ∣ k := Nat.dvd_of_mem_divisors hd
    obtain ⟨n, hn⟩ := hdk
    have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hn; omega)
    have hkd : k / d = n := by rw [hn]; exact Nat.mul_div_cancel_left n hd0
    rw [hkd, mul_sum]
    symm
    refine Finset.sum_nbij (fun j => d * j) ?_ ?_ ?_ ?_
    · intro j hj
      rw [mem_filter, mem_range]
      rw [mem_range] at hj
      exact ⟨hn ▸ Nat.mul_lt_mul_of_pos_left hj hd0, dvd_mul_right d j⟩
    · intro a _ b _ hab; exact Nat.eq_of_mul_eq_mul_left hd0 hab
    · intro x hx
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hx
      obtain ⟨hlt, j, rfl⟩ := hx
      refine ⟨j, ?_, rfl⟩
      simp only [mem_coe, mem_range]
      rw [hn] at hlt
      exact Nat.lt_of_mul_lt_mul_left hlt
    · intro j _
      rw [Nat.cast_mul, map_mul, mul_assoc]
      congr 2
      have : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
      rw [hn]
      push_cast; field_simp
  rw [sum_congr rfl (fun d hd => by rw [h3 d hd])]
  -- step 4: only d = k/r survives
  have hkr : k / r ∈ k.divisors := Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd h, by omega⟩
  have h4 : ∀ d ∈ k.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
      (ψ (d : ZMod r) * ∑ j ∈ range (k / d), ψ (j : ZMod r) * eC ((j : ℝ) / (k / d : ℕ))) =
      if d = k / r then ((ArithmeticFunction.moebius d : ℤ) : ℂ) * ψ (d : ZMod r) *
        ∑ j ∈ range r, ψ (j : ZMod r) * eC ((j : ℝ) * ((1 : ℤ) : ℝ) / r) else 0 := by
    intro d hd
    have hdk : d ∣ k := Nat.dvd_of_mem_divisors hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    by_cases hc : Nat.Coprime d r
    · have hrkd : r ∣ k / d := by
        have hk' : k = d * (k / d) := (Nat.mul_div_cancel' hdk).symm
        exact hc.symm.dvd_of_dvd_mul_left (hk' ▸ h)
      obtain ⟨s, hs⟩ := hrkd
      have hspos : 1 ≤ s := by
        rcases Nat.eq_zero_or_pos s with h0 | h0
        · rw [h0, mul_zero] at hs
          have := Nat.div_pos (Nat.le_of_dvd (by omega) hdk) hd0
          omega
        · exact h0
      by_cases hs1 : s = 1
      · have hdr : d = k / r := by
          subst hs1
          rw [mul_one] at hs
          rw [← hs, Nat.div_div_self hdk (by omega)]
        rw [ite_eq_left_of_eq_true _ _ (eq_true hdr), hs, hs1, mul_one]
        push_cast
        simp_rw [mul_one]
        ring
      · have hdr : d ≠ k / r := by
          intro hdr
          apply hs1
          have : k / d = r := by rw [hdr, Nat.div_div_self h (by omega)]
          rw [this] at hs
          have := (Nat.mul_eq_left (by omega : r ≠ 0)).mp hs.symm
          exact this
        rw [ite_eq_right_of_eq_false _ _ (eq_false hdr), hs, mv52_vanish ψ s hr hspos hs1]
        simp
    · have hz : ψ (d : ZMod r) = 0 :=
        MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
      rw [hz]; simp
  rw [sum_congr rfl h4, sum_ite_eq' k.divisors (k / r), ite_eq_left_of_eq_true _ _ (eq_true hkr)]


/-- P0015 Lemma 5.3 proof, page 358, PROVED: "Clearly `χ*(m) c_χ(m) = χ(m) c_χ(m) =
c_χ(1)`", the substitution `h ↦ hm` in display (2.1) for `(m, k) = 1`; here for any character
`χ` mod `k`, the second equality. -/
theorem mv_lemma53_shift : ∀ (k : ℕ) (χ : DirichletCharacter ℂ k), 1 ≤ k → ∀ m : ℤ,
    IsCoprime m k → χ (m : ZMod k) * rem66_cchi χ m = rem66_cchi χ 1 := by
  intro k χ hk m hm
  have : NeZero k := ⟨by omega⟩
  rw [rem66_cchi_eq_gaussSum_mulShift, rem66_cchi_one_eq_gaussSum,
    ← ZMod.coe_unitOfIsCoprime m hm, gaussSum_mulShift_eq, ← mul_assoc,
    MulChar.inv_apply_eq_inv']
  have h0 : χ ((ZMod.unitOfIsCoprime m hm : (ZMod k)ˣ) : ZMod k) ≠ 0 := by
    intro h0
    have := DirichletCharacter.unit_norm_eq_one χ (ZMod.unitOfIsCoprime m hm)
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  rw [mul_inv_cancel₀ h0, one_mul]

/-- P0015 Lemma 5.3, page 358, PROVED from its one line proof `mv_lemma53_shift` and Lemma 5.2:
for `χ` mod `k` induced by the primitive `χ*` mod `r` and `(m, k) = 1`,
`c_χ(m) = χ̄*(m) μ(k/r) χ*(k/r) τ(χ*)`. -/
theorem mv_lemma53 (H52 : type_of% @mv_lemma52)
    (r k : ℕ) (ψ : DirichletCharacter ℂ r) (h : r ∣ k) (hk : 1 ≤ k) (hp : ψ.IsPrimitive)
    (m : ℤ) (hm : IsCoprime m k) :
    rem66_cchi (changeLevel h ψ) m =
      ψ⁻¹ (m : ZMod r) * ((ArithmeticFunction.moebius (k / r) : ℤ) : ℂ) *
        ψ ((k / r : ℕ) : ZMod r) * rem66_cchi ψ 1 := by
  have s := mv_lemma53_shift k (changeLevel h ψ) hk m hm
  rw [changeLevel_eq_cast_of_dvd' ψ h hm, H52 r k ψ h hk hp] at s
  have hmr : IsCoprime m (r : ℤ) := hm.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr h)
  have hu : IsUnit ((m : ℤ) : ZMod r) := by
    rw [← ZMod.coe_unitOfIsCoprime m hmr]; exact Units.isUnit _
  have hinv : ψ⁻¹ (m : ZMod r) * ψ (m : ZMod r) = 1 := by
    rw [MulChar.inv_apply_eq_inv']
    have : ψ (m : ZMod r) ≠ 0 := by
      intro h0
      have := DirichletCharacter.unit_norm_eq_one ψ hu.unit
      rw [IsUnit.unit_spec, h0, norm_zero] at this
      exact zero_ne_one this
    exact inv_mul_cancel₀ this
  calc rem66_cchi (changeLevel h ψ) m
      = ψ⁻¹ (m : ZMod r) * (ψ (m : ZMod r) * rem66_cchi (changeLevel h ψ) m) := by
        rw [← mul_assoc, hinv, one_mul]
    _ = _ := by rw [s]; ring

/-- P0015 Lemma 5.4 proof, Case 1, page 359, PROVED through Mathlib's
`factorsThrough_of_gaussSum_ne_zero`, the argument of the paper. With `q₁ = q/(q,|m|)` and `χ`
mod `q` induced by the primitive `χ*` mod `r`, here `r = χ.conductor`: if `r ∤ q₁` then
`S(b) = 0` for every `(b, q₁) = 1` in (5.3), so `c_χ(m) = 0`. -/
theorem mv_lemma54_case1 : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), 1 ≤ q → ∀ m : ℤ,
    ¬ χ.conductor ∣ q / Nat.gcd q m.natAbs → rem66_cchi χ m = 0 := by
  intro q χ hq m hnd
  have : NeZero q := ⟨by omega⟩
  rw [rem66_cchi_eq_gaussSum_mulShift]
  by_contra hne
  apply hnd
  set g := Nat.gcd q m.natAbs with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hq1dvd : q / g ∣ q := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  have he : (ZMod.stdAddChar.mulShift (m : ZMod q)).mulShift ((q / g : ℕ) : ZMod q) = 1 := by
    rw [AddChar.mulShift_mulShift]
    have hz : (m : ZMod q) * ((q / g : ℕ) : ZMod q) = 0 := by
      obtain ⟨t, ht⟩ : (g : ℤ) ∣ m := Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _)
      have hgq : g * (q / g) = q := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have hgq' : (g : ℤ) * ((q / g : ℕ) : ℤ) = q := by exact_mod_cast hgq
      rw [← Int.cast_natCast (R := ZMod q) (q / g), ← Int.cast_mul,
        ZMod.intCast_zmod_eq_zero_iff_dvd, ht]
      exact ⟨t, by linear_combination t * hgq'⟩
    rw [hz, AddChar.mulShift_zero]
  have hf := factorsThrough_of_gaussSum_ne_zero _ hq1dvd he hne
  exact conductor_dvd_of_mem_conductorSet χ ((mem_conductorSet_iff χ).mpr hf)

/-- P0015 Lemma 5.4 proof, Case 2, page 359, the count behind `S(b) = χ*(b) φ(q)/φ(q₁)`,
PROVED: summing over the reduced residues mod `q` a function of the residue mod `q₁ | q`
gives the number of reduced residues mod `q` above `1` times the sum over reduced residues
mod `q₁`, since the reduction map on units is onto and its fibres are cosets. -/
theorem mv_case2_fiber_sum {q q₁ : ℕ} [NeZero q] [NeZero q₁] (hdvd : q₁ ∣ q) (H : ZMod q₁ → ℂ) :
    ∑ a : ZMod q, (if IsUnit a then H (ZMod.castHom hdvd (ZMod q₁) a) else 0) =
      ((univ.filter (fun a : ZMod q => IsUnit a ∧ ZMod.castHom hdvd (ZMod q₁) a = 1)).card : ℂ) *
        ∑ b : ZMod q₁, (if IsUnit b then H b else 0) := by
  classical
  set pr := ZMod.castHom hdvd (ZMod q₁) with hpr
  rw [← Finset.sum_fiberwise univ pr, mul_sum]
  refine sum_congr rfl (fun b _ => ?_)
  have hin : ∑ a ∈ univ.filter (fun a => pr a = b), (if IsUnit a then H (pr a) else 0) =
      ∑ a ∈ univ.filter (fun a => pr a = b), (if IsUnit a then H b else 0) := by
    refine sum_congr rfl (fun a ha => ?_)
    rw [(mem_filter.mp ha).2]
  rw [hin, ← sum_filter, filter_filter]
  by_cases hb : IsUnit b
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hb), sum_const, nsmul_eq_mul]
    congr 2
    obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hdvd hb.unit
    have hu' : pr (u : ZMod q) = b := by
      have := congrArg (fun v : (ZMod q₁)ˣ => (v : ZMod q₁)) hu
      simpa [ZMod.unitsMap_def, hpr] using this
    refine Finset.card_nbij' (fun a => ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * a) (fun a => (u : ZMod q) * a)
      ?_ ?_ ?_ ?_
    · intro a ha
      simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at ha ⊢
      refine ⟨(Units.isUnit _).mul ha.2, ?_⟩
      rw [map_mul, ha.1]
      have : pr ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * pr (u : ZMod q) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      rw [hu'] at this; exact this
    · intro a ha
      simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at ha ⊢
      refine ⟨by rw [map_mul, ha.2, hu', mul_one], (Units.isUnit _).mul ha.1⟩
    · intro a _
      simp only [← mul_assoc, Units.mul_inv, one_mul]
    · intro a _
      simp only [← mul_assoc, Units.inv_mul, one_mul]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hb)]
    rw [show (univ.filter (fun a : ZMod q => pr a = b ∧ IsUnit a)) = ∅ from ?_]
    · simp
    · ext a
      simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
      intro hab ha
      exact hb (hab ▸ ha.map pr)

/-- P0015 Lemma 5.4 proof, Case 2, pages 359 and 360, PROVED. With
`q₁ = q/(q,|m|)`, `m/q = m₁/q₁`, and `χ` mod `q` induced by the primitive `χ*` mod `r`: if
`r | q₁` then `S(b) = χ*(b) φ(q)/φ(q₁)` and `c_χ(m) = φ(q)/φ(q₁) c_{χ₁}(m₁)`, where `χ₁` is the
character mod `q₁` induced by `χ*`, here `changeLevel hd χ.primitiveCharacter`. -/
theorem mv_lemma54_case2 : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), 1 ≤ q → ∀ m : ℤ,
    ∀ hd : χ.conductor ∣ q / Nat.gcd q m.natAbs,
    rem66_cchi χ m =
      ((q.totient : ℂ) / ((q / Nat.gcd q m.natAbs).totient : ℂ)) *
        rem66_cchi (changeLevel hd χ.primitiveCharacter) (m / (Nat.gcd q m.natAbs : ℤ)) := by
  classical
  intro q χ hq m hd
  set g := Nat.gcd q m.natAbs with hg
  set q₁ := q / g with hq₁def
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hgq : g * q₁ = q := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hq₁pos : 0 < q₁ := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)) hgpos
  have : NeZero q := ⟨by omega⟩
  have : NeZero q₁ := ⟨by omega⟩
  have hq₁q : q₁ ∣ q := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  obtain ⟨t, ht⟩ : (g : ℤ) ∣ m := Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _)
  have hmt : m / (g : ℤ) = t := by
    rw [ht]; exact Int.mul_ediv_cancel_left t (by exact_mod_cast hgpos.ne')
  rw [hmt]
  set ψ := χ.primitiveCharacter
  set χ₁ := changeLevel hd ψ with hχ₁
  have hχ : χ = changeLevel hq₁q χ₁ := by
    rw [hχ₁, ← changeLevel_trans]; exact (changeLevel_primitiveCharacter χ).symm
  set pr := ZMod.castHom hq₁q (ZMod q₁) with hpr
  set G : ZMod q₁ → ℂ := fun b => χ₁ b * (ZMod.stdAddChar.mulShift (t : ZMod q₁)) b with hG
  have hterm : ∀ a : ZMod q, χ a * (ZMod.stdAddChar.mulShift (m : ZMod q)) a =
      if IsUnit a then G (pr a) else 0 := by
    intro a
    by_cases ha : IsUnit a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ha), hG]
      simp only
      congr 1
      · rw [hχ, ← ha.unit_spec, changeLevel_eq_cast_of_dvd, hpr, ZMod.castHom_apply]
      · rw [AddChar.mulShift_apply, AddChar.mulShift_apply, hpr, ZMod.castHom_apply,
          ZMod.cast_eq_val]
        have e1 : (m : ZMod q) * a = ((m * a.val : ℤ) : ZMod q) := by
          push_cast; rw [ZMod.natCast_zmod_val]
        have e2 : (t : ZMod q₁) * ((a.val : ℕ) : ZMod q₁) = ((t * a.val : ℤ) : ZMod q₁) := by
          push_cast; rfl
        rw [e1, e2, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
        congr 1
        have hg0 : (g : ℂ) ≠ 0 := by exact_mod_cast hgpos.ne'
        have hq0 : (q₁ : ℂ) ≠ 0 := by exact_mod_cast hq₁pos.ne'
        have hqC : (q : ℂ) = (g : ℂ) * q₁ := by exact_mod_cast hgq.symm
        rw [ht, hqC]
        push_cast
        field_simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false ha), MulChar.map_nonunit _ ha, zero_mul]
  have hN := mv_case2_fiber_sum hq₁q G
  have hφ := mv_case2_fiber_sum hq₁q (fun _ => (1 : ℂ))
  have hcount : ∀ n : ℕ, [NeZero n] →
      ∑ a : ZMod n, (if IsUnit a then (1 : ℂ) else 0) = (n.totient : ℂ) := by
    intro n _
    have h := MulChar.sum_one_eq_card_units (R := ZMod n) (R' := ℂ)
    rw [ZMod.card_units_eq_totient] at h
    rw [← h]
    refine sum_congr rfl (fun a _ => ?_)
    by_cases ha : IsUnit a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ha), MulChar.one_apply ha]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false ha), MulChar.map_nonunit _ ha]
  rw [hcount q, hcount q₁] at hφ
  set N := ((univ.filter (fun a : ZMod q => IsUnit a ∧ pr a = 1)).card : ℂ)
  have hφ1 : (q₁.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq₁pos).ne'
  have hNval : N = (q.totient : ℂ) / (q₁.totient : ℂ) := by
    rw [hφ]; field_simp
  have hG0 : ∑ b : ZMod q₁, (if IsUnit b then G b else 0) = ∑ b : ZMod q₁, G b := by
    refine sum_congr rfl (fun b _ => ?_)
    by_cases hb : IsUnit b
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hb), hG]; simp only; rw [MulChar.map_nonunit _ hb, zero_mul]
  rw [rem66_cchi_eq_gaussSum_mulShift, rem66_cchi_eq_gaussSum_mulShift]
  unfold gaussSum
  rw [sum_congr rfl (fun a _ => hterm a), hN, hG0, hNval]


/-- P0015 Lemma 5.4, display (5.1), pages 358 to 360, PROVED from Case 1, Case 2 and
Lemma 5.3, "But `(m₁, q₁) = 1`, so (5.1) now follows from Lemma 5.3". Let `χ` be a character
mod `q` induced by the primitive character `χ*` mod `r`, here `χ*` is `χ.primitiveCharacter`
and `r` is `χ.conductor`. For an arbitrary integer `m` put `q₁ = q/(q, |m|)`. If `r ∤ q₁` then
`c_χ(m) = 0`. If `r | q₁` then `c_χ(m) = χ̄*(m/(q,|m|)) φ(q)/φ(q₁) μ(q₁/r) χ*(q₁/r) τ(χ*)`. -/
theorem mv_lemma54_of (H52 : type_of% @mv_lemma52)
    :
    ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), 1 ≤ q → ∀ m : ℤ,
    (¬ χ.conductor ∣ q / Nat.gcd q m.natAbs → rem66_cchi χ m = 0) ∧
    (χ.conductor ∣ q / Nat.gcd q m.natAbs →
      rem66_cchi χ m =
        χ.primitiveCharacter⁻¹ (((m / (Nat.gcd q m.natAbs : ℤ) : ℤ)) : ZMod χ.conductor) *
          ((q.totient : ℂ) / ((q / Nat.gcd q m.natAbs).totient : ℂ)) *
          ((ArithmeticFunction.moebius (q / Nat.gcd q m.natAbs / χ.conductor) : ℤ) : ℂ) *
          χ.primitiveCharacter ((q / Nat.gcd q m.natAbs / χ.conductor : ℕ) : ZMod χ.conductor) *
          rem66_cchi χ.primitiveCharacter 1) := by
  intro q χ hq m
  refine ⟨mv_lemma54_case1 q χ hq m, fun hd => ?_⟩
  set g := Nat.gcd q m.natAbs with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hq₁ : 1 ≤ q / g := Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)) hgpos
  obtain ⟨t, ht⟩ : (g : ℤ) ∣ m := Int.natCast_dvd.mpr (Nat.gcd_dvd_right _ _)
  have hmt : m / (g : ℤ) = t := by
    rw [ht]; exact Int.mul_ediv_cancel_left t (by exact_mod_cast hgpos.ne')
  have hcop : IsCoprime (m / (g : ℤ)) ((q / g : ℕ) : ℤ) := by
    rw [hmt, Int.isCoprime_iff_gcd_eq_one]
    have hna : m.natAbs = g * t.natAbs := by rw [ht, Int.natAbs_mul]; rfl
    have ht' : t.natAbs = m.natAbs / g := by
      rw [hna]; exact (Nat.mul_div_cancel_left _ hgpos).symm
    change Nat.gcd t.natAbs (q / g) = 1
    rw [ht', Nat.gcd_comm]
    exact Nat.coprime_div_gcd_div_gcd hgpos
  rw [mv_lemma54_case2 q χ hq m hd, mv_lemma53 H52 χ.conductor (q / g) χ.primitiveCharacter hd hq₁
    (primitiveCharacter_isPrimitive χ) _ hcop]
  ring

/-! ### Consequences in norm form -/

/-- From Lemmas 5.1 and 5.2, PROVED: `|τ(χ̄χ₀)| ≤ r^{1/2}`, and `τ(χ̄χ₀) = 0` unless
`(q/r, r) = 1` and `μ(q/r)² = 1`, as used on page 360. -/
theorem mv_tau_bound (H52 : type_of% @mv_lemma52)
    (r q : ℕ) (ψ : DirichletCharacter ℂ r) (h : r ∣ q) (hr : 1 ≤ r) (hq : 1 ≤ q)
    (hp : ψ.IsPrimitive) :
    ‖rem66_cchi (changeLevel h ψ)⁻¹ 1‖ ≤
      (if Nat.Coprime (q / r) r ∧ Squarefree (q / r) then Real.sqrt r else 0) := by
  have hinv : (changeLevel h ψ)⁻¹ = changeLevel h ψ⁻¹ := (map_inv _ _).symm
  have hpi : ψ⁻¹.IsPrimitive := by
    rw [isPrimitive_def, conductor_inv]; exact hp
  rw [hinv, H52 r q ψ⁻¹ h hq hpi, norm_mul, norm_mul]
  have h51 := mv_lemma51_norm_le r ψ⁻¹ hr
  split_ifs with hc
  · have h1 : ‖((ArithmeticFunction.moebius (q / r) : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have h2 : ‖ψ⁻¹ ((q / r : ℕ) : ZMod r)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
    calc _ ≤ 1 * 1 * Real.sqrt r := by gcongr
      _ = _ := by ring
  · rw [not_and_or] at hc
    rcases hc with hc | hc
    · have : ψ⁻¹ ((q / r : ℕ) : ZMod r) = 0 :=
        MulChar.map_nonunit _ (fun hu => hc ((ZMod.isUnit_iff_coprime _ _).mp hu))
      simp [this]
    · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hc]

/-- From Lemmas 5.1 and 5.4, PROVED: with `q₁ = q/(q,|m|)` and `r₃` the conductor of `χ`,
`|c_χ(m)| ≤ r₃^{1/2} φ(q)/φ(q₁)` if `r₃ | q₁`, and `c_χ(m) = 0` otherwise. -/
theorem mv_cchi_bound (H52 : type_of% @mv_lemma52)
   
    (q : ℕ) (χ : DirichletCharacter ℂ q) (hq : 1 ≤ q) (m : ℤ) :
    ‖rem66_cchi χ m‖ ≤
      (if χ.conductor ∣ q / Nat.gcd q m.natAbs then
        Real.sqrt χ.conductor * ((q.totient : ℝ) / ((q / Nat.gcd q m.natAbs).totient : ℝ))
      else 0) := by
  obtain ⟨h0, h1⟩ := mv_lemma54_of H52 q χ hq m
  split_ifs with hc
  · rw [h1 hc]
    have hc1 : 1 ≤ χ.conductor := by
      rcases Nat.eq_zero_or_pos χ.conductor with h | h
      · exact absurd (conductor_eq_zero_iff_level_eq_zero.mp h) (by omega)
      · exact h
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    have h51 := mv_lemma51_norm_le _ χ.primitiveCharacter hc1
    have e1 : ‖χ.primitiveCharacter⁻¹ (((m / (Nat.gcd q m.natAbs : ℤ) : ℤ)) :
        ZMod χ.conductor)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
    have e2 : ‖((ArithmeticFunction.moebius (q / Nat.gcd q m.natAbs / χ.conductor) : ℤ) :
        ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have e3 : ‖χ.primitiveCharacter ((q / Nat.gcd q m.natAbs / χ.conductor : ℕ) :
        ZMod χ.conductor)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
    have e4 : ‖((q.totient : ℂ) / ((q / Nat.gcd q m.natAbs).totient : ℂ))‖ =
        (q.totient : ℝ) / ((q / Nat.gcd q m.natAbs).totient : ℝ) := by
      rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
    rw [e4]
    have h5 : 0 ≤ (q.totient : ℝ) / ((q / Nat.gcd q m.natAbs).totient : ℝ) := by positivity
    calc _ ≤ 1 * ((q.totient : ℝ) / ((q / Nat.gcd q m.natAbs).totient : ℝ)) * 1 * 1 *
          Real.sqrt χ.conductor := by gcongr
      _ = _ := by ring
  · rw [h0 hc, norm_zero]

/-! ### The arithmetic of page 360, PROVED -/

/-- P0015 page 360, PROVED: "If `q` gives rise to a non-zero term in the sum then
`(q/rᵢ, rᵢ) = 1` and `μ(q/rᵢ)² = 1`, `i = 1, 2`, from which we deduce that `(k, r₄) = 1` and
`μ(k)² = 1`", with `q = r₄ k`, `r₄ = [r₁, r₂]`. -/
theorem mv_p360_k_coprime (r₁ r₂ q : ℕ) (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂)
    (h₁ : r₁ ∣ q) (h₂ : r₂ ∣ q)
    (c₁ : Nat.Coprime (q / r₁) r₁ ∧ Squarefree (q / r₁))
    (c₂ : Nat.Coprime (q / r₂) r₂ ∧ Squarefree (q / r₂)) :
    Nat.Coprime (q / Nat.lcm r₁ r₂) (Nat.lcm r₁ r₂) ∧ Squarefree (q / Nat.lcm r₁ r₂) := by
  set r₄ := Nat.lcm r₁ r₂
  have h4 : r₄ ∣ q := Nat.lcm_dvd h₁ h₂
  obtain ⟨k, hk⟩ := h4
  have hr₄ : 0 < r₄ := Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))
  have hqk : q / r₄ = k := by rw [hk]; exact Nat.mul_div_cancel_left k hr₄
  obtain ⟨t₁, ht₁⟩ := Nat.dvd_lcm_left r₁ r₂
  obtain ⟨t₂, ht₂⟩ := Nat.dvd_lcm_right r₁ r₂
  have hq₁ : q / r₁ = t₁ * k := by
    rw [hk, show r₄ = r₁ * t₁ from ht₁, mul_assoc]; exact Nat.mul_div_cancel_left _ (by omega)
  have hq₂ : q / r₂ = t₂ * k := by
    rw [hk, show r₄ = r₂ * t₂ from ht₂, mul_assoc]; exact Nat.mul_div_cancel_left _ (by omega)
  rw [hqk]
  have hd₁ : k ∣ q / r₁ := hq₁ ▸ dvd_mul_left k t₁
  have hd₂ : k ∣ q / r₂ := hq₂ ▸ dvd_mul_left k t₂
  refine ⟨?_, c₁.2.squarefree_of_dvd hd₁⟩
  have k1 : Nat.Coprime k r₁ := Nat.Coprime.coprime_dvd_left hd₁ c₁.1
  have k2 : Nat.Coprime k r₂ := Nat.Coprime.coprime_dvd_left hd₂ c₂.1
  exact Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul r₁ r₂) (Nat.Coprime.mul_right k1 k2)

/-- P0015 page 360, PROVED: for `q = r₄ k` with `(k, r₄) = 1`,
`q/(q,m) = (r₄/r₅)(k/(k,m))` with `r₅ = (r₄, m)`, and the two factors are coprime; so
`φ(q/(q,m)) = φ(k/(k,m)) φ(r₄/r₅)`. -/
theorem mv_p360_q1 (r₄ k n : ℕ) (hc : Nat.Coprime k r₄) :
    (r₄ * k) / Nat.gcd (r₄ * k) n = (r₄ / Nat.gcd r₄ n) * (k / Nat.gcd k n) ∧
      Nat.Coprime (r₄ / Nat.gcd r₄ n) (k / Nat.gcd k n) := by
  have hg : Nat.gcd (r₄ * k) n = Nat.gcd r₄ n * Nat.gcd k n := by
    rw [Nat.gcd_comm, Nat.Coprime.gcd_mul n hc.symm, Nat.gcd_comm n r₄, Nat.gcd_comm n k]
  refine ⟨?_, ?_⟩
  · rw [hg, Nat.div_mul_div_comm (Nat.gcd_dvd_left r₄ n) (Nat.gcd_dvd_left k n)]
  · exact Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left r₄ n))
      (Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left k n)) hc.symm)

/-- P0015 page 360, PROVED: "Clearly `r₃ | r₄`": the conductor of `χ₁χ₂χ₀` divides `[r₁, r₂]`. -/
theorem mv_p360_r3_dvd (r₁ r₂ q : ℕ) (ψ₁ : DirichletCharacter ℂ r₁)
    (ψ₂ : DirichletCharacter ℂ r₂) (hq : 1 ≤ q) (h : r₁ ∣ q ∧ r₂ ∣ q) :
    (changeLevel h.1 ψ₁ * changeLevel h.2 ψ₂).conductor ∣ Nat.lcm r₁ r₂ := by
  have : NeZero q := ⟨by omega⟩
  have h4 : Nat.lcm r₁ r₂ ∣ q := Nat.lcm_dvd h.1 h.2
  have e : changeLevel h.1 ψ₁ * changeLevel h.2 ψ₂ = changeLevel h4
      (changeLevel (Nat.dvd_lcm_left r₁ r₂) ψ₁ * changeLevel (Nat.dvd_lcm_right r₁ r₂) ψ₂) := by
    rw [map_mul, ← changeLevel_trans, ← changeLevel_trans]
  rw [e]
  exact conductor_dvd_of_mem_conductorSet _ ((mem_conductorSet_iff _).mpr
    (changeLevel_factorsThrough _ _))

/-! ### Assembly of display (5.5) termwise -/

/-- P0015 Lemma 5.5 proof, display (5.5) termwise, page 360, PROVED sorry free from
Lemmas 5.1, 5.3 and 5.4, proved here, and Lemma 5.2 as a hypothesis: the exact statement of
`lem55_termwise`, with the absolute constant `C = 1`. -/
theorem lem55_termwise_of_leaves (H52 : type_of% @mv_lemma52)
    :
    type_of% @lem55_termwise := by
  classical
  refine ⟨1, one_pos, ?_⟩
  intro r₁ r₂ ψ₁ ψ₂ hr₁ hr₂ hp₁ hp₂ m hm q hq h
  set r₄ := Nat.lcm r₁ r₂ with hr₄def
  set n := m.natAbs with hn
  set χ := changeLevel h.1 ψ₁ * changeLevel h.2 ψ₂ with hχ
  have hr₄ : 0 < r₄ := Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))
  have hn0 : n ≠ 0 := Int.natAbs_ne_zero.mpr hm
  have hb₁ := mv_tau_bound H52 r₁ q ψ₁ h.1 hr₁ hq hp₁
  have hb₂ := mv_tau_bound H52 r₂ q ψ₂ h.2 hr₂ hq hp₂
  have hcb := mv_cchi_bound H52 q χ hq m
  rw [← hn] at hcb
  rw [norm_mul, norm_mul]
  set X := ‖rem66_cchi χ m‖
  set Y := ‖rem66_cchi (changeLevel h.1 ψ₁)⁻¹ 1‖
  set Z := ‖rem66_cchi (changeLevel h.2 ψ₂)⁻¹ 1‖
  have hX0 : 0 ≤ X := norm_nonneg _
  have hY0 : 0 ≤ Y := norm_nonneg _
  have hZ0 : 0 ≤ Z := norm_nonneg _
  set k := q / r₄ with hkdef
  have hqk : q = r₄ * k := (Nat.mul_div_cancel' (Nat.lcm_dvd h.1 h.2)).symm
  have hRHS : 0 ≤ (1 : ℝ) * (Real.sqrt ((r₁ : ℝ) * r₂ * r₄ / (Nat.gcd r₄ n)) /
      ((r₄.totient : ℝ) * ((r₄ / Nat.gcd r₄ n).totient : ℝ))) *
      (if Nat.Coprime k r₄ ∧ Squarefree k then
        1 / ((k.totient : ℝ) * ((k / Nat.gcd k n).totient : ℝ)) else 0) := by
    have : 0 ≤ (if Nat.Coprime k r₄ ∧ Squarefree k then
        1 / ((k.totient : ℝ) * ((k / Nat.gcd k n).totient : ℝ)) else (0 : ℝ)) := by
      split_ifs <;> positivity
    positivity
  by_cases c₁ : Nat.Coprime (q / r₁) r₁ ∧ Squarefree (q / r₁)
  swap
  · rw [ite_eq_right_of_eq_false _ _ (eq_false c₁)] at hb₁
    rw [show X * Y * Z = 0 by rw [le_antisymm hb₁ hY0]; ring, zero_div]; exact hRHS
  by_cases c₂ : Nat.Coprime (q / r₂) r₂ ∧ Squarefree (q / r₂)
  swap
  · rw [ite_eq_right_of_eq_false _ _ (eq_false c₂)] at hb₂
    rw [show X * Y * Z = 0 by rw [le_antisymm hb₂ hZ0]; ring, zero_div]; exact hRHS
  rw [ite_eq_left_of_eq_true _ _ (eq_true c₁)] at hb₁
  rw [ite_eq_left_of_eq_true _ _ (eq_true c₂)] at hb₂
  have hk := mv_p360_k_coprime r₁ r₂ q hr₁ hr₂ h.1 h.2 c₁ c₂
  rw [ite_eq_left_of_eq_true _ _ (eq_true hk)] at hRHS ⊢
  by_cases c₃ : χ.conductor ∣ q / Nat.gcd q n
  swap
  · rw [ite_eq_right_of_eq_false _ _ (eq_false c₃)] at hcb
    rw [show X * Y * Z = 0 by rw [le_antisymm hcb hX0]; ring, zero_div]; exact hRHS
  rw [ite_eq_left_of_eq_true _ _ (eq_true c₃)] at hcb
  -- the arithmetic of page 360
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, mul_zero] at hqk; omega
    · exact h0
  obtain ⟨hq1, hcop⟩ := mv_p360_q1 r₄ k n hk.1
  set A := r₄ / Nat.gcd r₄ n with hA
  set B := k / Nat.gcd k n with hB
  have hApos : 0 < A := Nat.div_pos (Nat.le_of_dvd hr₄ (Nat.gcd_dvd_left r₄ n))
    (Nat.gcd_pos_of_pos_left _ hr₄)
  have hBpos : 0 < B := Nat.div_pos (Nat.le_of_dvd hkpos (Nat.gcd_dvd_left k n))
    (Nat.gcd_pos_of_pos_left _ hkpos)
  have hq1' : q / Nat.gcd q n = A * B := by rw [hqk]; exact hq1
  have hφq : q.totient = r₄.totient * k.totient := by
    rw [hqk]; exact Nat.totient_mul hk.1.symm
  have hφq1 : (q / Nat.gcd q n).totient = A.totient * B.totient := by
    rw [hq1']; exact Nat.totient_mul hcop
  have hr3 : χ.conductor ∣ r₄ := mv_p360_r3_dvd r₁ r₂ q ψ₁ ψ₂ hq h
  have hr3B : Nat.Coprime χ.conductor B :=
    Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left k n))
      (Nat.Coprime.coprime_dvd_left hr3 hk.1.symm)
  have hr3A : χ.conductor ∣ A := by
    rw [hq1'] at c₃; exact hr3B.dvd_of_dvd_mul_right c₃
  have hr3le : (χ.conductor : ℝ) ≤ A := by exact_mod_cast Nat.le_of_dvd hApos hr3A
  have hAR : ((r₁ : ℝ) * r₂ * r₄ / (Nat.gcd r₄ n)) = (r₁ : ℝ) * r₂ * A := by
    have hg0 : ((Nat.gcd r₄ n : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.gcd_pos_of_pos_left _ hr₄).ne'
    rw [hA, Nat.cast_div (Nat.gcd_dvd_left r₄ n) hg0, mul_div_assoc]
  rw [hAR]
  rw [hφq1] at hcb
  rw [hφq] at hcb ⊢
  have ha : 0 < (r₄.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hr₄
  have hb : 0 < (k.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hkpos
  have hc : 0 < (A.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hApos
  have hd : 0 < (B.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hBpos
  push_cast at hcb ⊢
  set a := (r₄.totient : ℝ)
  set b := (k.totient : ℝ)
  set c := (A.totient : ℝ)
  set d := (B.totient : ℝ)
  have hS : Real.sqrt χ.conductor * Real.sqrt r₁ * Real.sqrt r₂ ≤
      Real.sqrt ((r₁ : ℝ) * r₂ * A) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    nlinarith [show (0 : ℝ) ≤ (r₁ : ℝ) * r₂ by positivity]
  have hS0 : 0 ≤ Real.sqrt χ.conductor := Real.sqrt_nonneg _
  calc X * Y * Z / (a * b) ^ 2
      ≤ Real.sqrt χ.conductor * (a * b / (c * d)) * Real.sqrt r₁ * Real.sqrt r₂ /
          (a * b) ^ 2 := by gcongr
    _ = (Real.sqrt χ.conductor * Real.sqrt r₁ * Real.sqrt r₂) / (a * c * (b * d)) := by
          field_simp
    _ ≤ Real.sqrt ((r₁ : ℝ) * r₂ * A) / (a * c * (b * d)) := by gcongr
    _ = _ := by field_simp

/-- The exact statement of `lem55_termwise`, PROVED sorry free, from Lemma 5.2 `mv_lemma52`,
proved above. -/
theorem lem55_termwise_split : type_of% @lem55_termwise :=
  lem55_termwise_of_leaves mv_lemma52

/-- Twin check: `lem55_termwise_split` has exactly the type of `lem55_termwise`. -/
theorem lem55_termwise_split_twin : type_of% @lem55_termwise := lem55_termwise_split

end LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit

#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.lem55_termwise_of_leaves
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.lem55_termwise_split
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.mv_lemma51_norm_le
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.mv_lemma52
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.lem55_termwise_split_twin
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.mv_lemma54_of
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.mv_lemma53
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.mv_lemma53_shift
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.mv_lemma54_case1
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.mv_lemma54_case2
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.mv_p360_k_coprime
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.mv_p360_q1
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.mv_p360_r3_dvd
