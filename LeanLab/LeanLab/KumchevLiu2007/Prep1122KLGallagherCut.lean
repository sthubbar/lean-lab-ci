/-
BURST 2026-11-22 S35, unit P1122-0137. SPLIT of the LEAF
Prep1121DKLMajorCut.S2_sub_S2star_major_mean_square, the mean square of S2 - S2*
over the major arcs M. Kumchev and Liu 2007, P0088, arXiv 0801.0130, page 5
displays 15, 18 and 19 and page 6 display 20.

The printed argument, with Y = windowY X eps, P = (log X)^B and Q = H/P:
* page 4 display 15: the arcs M(q, a) are disjoint, so on the arc of q, a the
  function S2* is the single term S(q, a)/phi(q) T2(beta), beta = alpha - a/q.
  arc_localization, first a LEAF MEDIUM, PROVED in the same burst.
* page 5 display 18: (A2.1) puts the rough weight on m coprime to q, and the
  orthogonality of the characters modulo q bounds |S2 - S2*|^2 by the sum over
  chi of |W2(beta, chi)|^2. char_orthogonality_18, first a LEAF MEDIUM, PROVED
  in the same burst by the character expansion, Cauchy and Parseval.
* page 6 before display 20: Gallagher's lemma, reference 5 Lemma 1, with the
  device of Saffari and Vaughan, reference 21 page 25, bounds the integral of
  |W2|^2 over |beta| at most 1/(qQ) by (qQ)^(-2) times the mean square of
  (A2.2) plus delta, for some delta of size qQ/Y. LEAF
  gallagher_saffari_vaughan, HARD, a citation wall.
* hypothesis (A2.2), here A22Corr, then gives C P^(-4) for each chi; this
  combination is PROVED below as arc_char_mean_square.
* at most P characters and at most 2 P^2 arcs give C P^(-1), at most
  C P^(-1/2) as the parent states. PROVED below.

The final theorem S2_sub_S2star_major_mean_square_of_pieces proves the exact
statement of the parent leaf from the pieces, CONDITIONAL ON A22Corr, the
cited hypothesis (A2.2) of page 5. W2(beta, chi) of page 5 is written out in
each statement, with chi on the weight only as in A22Corr, so no new
definition is made.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1121DKLMajorCut

namespace LeanLab.KumchevLiu2007.Prep1122KLGallagherCut

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Prep1121KLMajor
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-! ## The leaves -/

/-! ## Display 18, character orthogonality, PROVED in burst-20261122 -/

lemma star_char_unit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ZMod q} (hx : IsUnit x) :
    star (χ x) = χ x⁻¹ := by
  have h1 : χ x * χ x⁻¹ = 1 := by rw [← map_mul, ZMod.mul_inv_of_unit _ hx, map_one]
  have h2 : ‖χ x‖ = 1 := χ.unit_norm_eq_one hx.unit
  rw [RCLike.star_def, ← Complex.inv_eq_conj h2]
  exact (eq_inv_of_mul_eq_one_right h1).symm

lemma orth {q : ℕ} [NeZero q] {x : ZMod q} (hx : IsUnit x) (y : ZMod q) :
    ∑ χ : DirichletCharacter ℂ q, star (χ x) * χ y = if x = y then (q.totient : ℂ) else 0 := by
  simp_rw [star_char_unit _ hx]
  exact DirichletCharacter.sum_char_inv_mul_char_eq ℂ hx y

lemma unit_of_coprime {q x : ℕ} (h : Nat.Coprime x q) : IsUnit (x : ZMod q) :=
  (ZMod.isUnit_iff_coprime x q).mpr h

lemma natCast_eq_iff_of_lt {q x y : ℕ} (hx : x < q) (hy : y < q) :
    ((x : ZMod q) = (y : ZMod q)) ↔ x = y := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

/-- Helper for P0088 page 3 display 8 and page 5 display 18: the residues x below q
coprime to q, the range of the Gauss sum S(q, a) as U1534.gaussS writes it. -/
noncomputable def cset (q : ℕ) : Finset ℕ := (Finset.range q).filter (fun x => Nat.Coprime x q)

lemma card_cset (q : ℕ) : (cset q).card = q.totient := by
  rw [Nat.totient_eq_card_coprime, cset]
  congr 1
  exact Finset.filter_congr (fun x _ => Nat.coprime_comm)

/-- P0088 page 5 display 18, the twisted Gauss sum: the sum over x below q coprime to q of
conj chi(x) e(a x^2/q), the coefficient of chi in the character expansion of e(a m^2/q). -/
noncomputable def Gs (q a : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ x ∈ cset q, star (χ x) * U1534.ee ((a * x ^ 2 : ℕ) / (q : ℝ))

lemma norm_ee (t : ℝ) : ‖U1534.ee t‖ = 1 := by
  unfold U1534.ee
  rw [Complex.norm_exp]
  simp

lemma Gs_one (q a : ℕ) [NeZero q] : Gs q a 1 = U1534.gaussS q a := by
  unfold Gs U1534.gaussS
  refine Finset.sum_congr rfl (fun x hx => ?_)
  have hx' : Nat.Coprime x q := (Finset.mem_filter.mp hx).2
  rw [MulChar.one_apply (unit_of_coprime hx')]
  simp

lemma key (q a : ℕ) [NeZero q] {m : ℕ} (hm : Nat.Coprime m q) :
    ∑ χ : DirichletCharacter ℂ q, Gs q a χ * χ m =
      (q.totient : ℂ) * U1534.ee ((a * (m % q) ^ 2 : ℕ) / (q : ℝ)) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  unfold Gs
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ x ∈ cset q, ∑ χ : DirichletCharacter ℂ q,
      star (χ x) * U1534.ee ((a * x ^ 2 : ℕ) / (q : ℝ)) * χ m =
      if x = m % q then (q.totient : ℂ) * U1534.ee ((a * x ^ 2 : ℕ) / (q : ℝ)) else 0 := by
    intro x hx
    rw [cset, Finset.mem_filter, Finset.mem_range] at hx
    have e1 : ∀ χ : DirichletCharacter ℂ q, star (χ x) * U1534.ee ((a * x ^ 2 : ℕ) / (q : ℝ)) * χ m
        = U1534.ee ((a * x ^ 2 : ℕ) / (q : ℝ)) * (star (χ x) * χ m) := fun χ => by ring
    simp_rw [e1]
    rw [← Finset.mul_sum, orth (unit_of_coprime hx.2)]
    have : ((x : ZMod q) = (m : ZMod q)) ↔ x = m % q := by
      rw [← ZMod.natCast_mod m q, natCast_eq_iff_of_lt hx.1 (Nat.mod_lt _ hq)]
    by_cases h : x = m % q
    · rw [if_pos (this.mpr h), if_pos h]; ring
    · rw [if_neg (fun h' => h (this.mp h')), if_neg h]; ring
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  rw [if_pos]
  rw [cset, Finset.mem_filter, Finset.mem_range]
  refine ⟨Nat.mod_lt _ hq, ?_⟩
  have := Nat.gcd_rec q m
  unfold Nat.Coprime at *
  rw [Nat.gcd_comm] at hm
  omega

lemma fourier_split (q a m : ℕ) (hq : 0 < q) (β : ℝ) :
    fourier ((m ^ 2 : ℕ) : ℤ) ((((a : ℝ) / q + β : ℝ)) : AddCircle (1 : ℝ)) =
      U1534.ee ((a * (m % q) ^ 2 : ℕ) / (q : ℝ)) * fourier ((m ^ 2 : ℕ) : ℤ) (β : AddCircle (1 : ℝ)) := by
  rw [fourier_coe_apply, fourier_coe_apply]
  unfold U1534.ee
  set r := m % q
  set t := m / q
  have hm : m = q * t + r := (Nat.div_add_mod m q).symm
  set K : ℕ := a * (2 * t * r + q * t ^ 2)
  have hnat : a * m ^ 2 = a * r ^ 2 + q * K := by rw [hm]; ring
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hK : ((m ^ 2 : ℕ) : ℂ) * ((a : ℂ) / q) = ((a * r ^ 2 : ℕ) : ℂ) / q + (K : ℂ) := by
    have : ((a * m ^ 2 : ℕ) : ℂ) = ((a * r ^ 2 + q * K : ℕ) : ℂ) := by rw [hnat]
    push_cast at this ⊢
    field_simp
    linear_combination this
  have e : 2 * ↑π * I * ((((m ^ 2 : ℕ) : ℤ) : ℂ)) * ((((a : ℝ) / q + β : ℝ)) : ℂ) / ((1 : ℝ) : ℂ) =
      2 * ↑π * I * ((((a * r ^ 2 : ℕ) : ℝ) / (q : ℝ) : ℝ) : ℂ) + (K : ℂ) * (2 * ↑π * I) +
      2 * ↑π * I * ((((m ^ 2 : ℕ) : ℤ) : ℂ)) * ((β : ℝ) : ℂ) / ((1 : ℝ) : ℂ) := by
    have hK' := hK
    push_cast at hK' ⊢
    linear_combination (2 * ↑π * I) * hK'
  rw [e, Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]


lemma parseval (q a : ℕ) [NeZero q] :
    ∑ χ : DirichletCharacter ℂ q, ‖Gs q a χ‖ ^ 2 = (q.totient : ℝ) ^ 2 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  set c : ℕ → ℂ := fun x => U1534.ee ((a * x ^ 2 : ℕ) / (q : ℝ))
  have hc : ∀ x, c x * star (c x) = 1 := by
    intro x
    rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_ee]; simp
  apply Complex.ofReal_injective
  push_cast
  have h1 : ∀ χ : DirichletCharacter ℂ q, ((‖Gs q a χ‖ : ℂ)) ^ 2 =
      ∑ x ∈ cset q, ∑ y ∈ cset q, c x * star (c y) * (star (χ x) * χ y) := by
    intro χ
    rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, ← RCLike.star_def]
    unfold Gs
    rw [star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [star_mul, star_star]; ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := cset q)]
  simp_rw [← Finset.mul_sum]
  have h2 : ∀ x ∈ cset q, ∑ y ∈ cset q, c x * star (c y) *
      ∑ χ : DirichletCharacter ℂ q, star (χ x) * χ y = (q.totient : ℂ) := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    rw [Finset.sum_eq_single x]
    · rw [orth (unit_of_coprime hx'.2), if_pos rfl, hc, one_mul]
    · intro y hy hyx
      have hy' := Finset.mem_filter.mp hy
      rw [orth (unit_of_coprime hx'.2), if_neg, mul_zero]
      rw [natCast_eq_iff_of_lt (Finset.mem_range.mp hx'.1) (Finset.mem_range.mp hy'.1)]
      exact fun h => hyx h.symm
    · intro h; exact absurd hx h
  rw [Finset.sum_congr rfl h2, Finset.sum_const, card_cset]
  simp [sq]


lemma cs_bound (q a : ℕ) [NeZero q] (w : DirichletCharacter ℂ q → ℂ) :
    ‖((q.totient : ℂ))⁻¹ * ∑ χ, Gs q a χ * w χ‖ ^ 2 ≤ ∑ χ, ‖w χ‖ ^ 2 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  rw [norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
  have h1 : ‖∑ χ, Gs q a χ * w χ‖ ^ 2 ≤ (∑ χ, ‖Gs q a χ‖ * ‖w χ‖) ^ 2 := by
    gcongr
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [norm_mul]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun χ => ‖Gs q a χ‖) (fun χ => ‖w χ‖)
  rw [parseval] at h2
  have h3 := h1.trans h2
  calc ((q.totient : ℝ))⁻¹ ^ 2 * ‖∑ χ, Gs q a χ * w χ‖ ^ 2
      ≤ ((q.totient : ℝ))⁻¹ ^ 2 * ((q.totient : ℝ) ^ 2 * ∑ χ, ‖w χ‖ ^ 2) := by gcongr
    _ = ∑ χ, ‖w χ‖ ^ 2 := by field_simp

lemma per_m (q a : ℕ) [NeZero q] (m : ℕ) (r f F : ℂ) (hr : r ≠ 0 → Nat.Coprime m q) :
    ∑ χ : DirichletCharacter ℂ q, Gs q a χ * ((r * χ m - (if χ = 1 then f else 0)) * F) =
      (q.totient : ℂ) * (r * (U1534.ee ((a * (m % q) ^ 2 : ℕ) / (q : ℝ)) * F)) -
        U1534.gaussS q a * (f * F) := by
  have e : ∀ χ : DirichletCharacter ℂ q, Gs q a χ * ((r * χ m - (if χ = 1 then f else 0)) * F) =
      r * F * (Gs q a χ * χ m) - (if χ = 1 then Gs q a χ * (f * F) else 0) := by
    intro χ; split_ifs <;> ring
  simp_rw [e]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ (1 : DirichletCharacter ℂ q),
    if_pos (Finset.mem_univ _), Gs_one]
  by_cases h0 : r = 0
  · simp [h0]
  · rw [key q a (hr h0)]; ring

/-- PROVED. P0088 page 5 display 18, orthogonality of the characters modulo q. Was LEAF MEDIUM.
Let alpha = a/q + beta with a coprime to q. When every m of the square window with a
nonzero rough weight is coprime to q, which is (A2.1) of page 4 as the paper notes
before display 18, expanding e(a m^2/q) over the characters modulo q writes
S2(alpha) - S(q, a)/phi(q) T2(beta) as phi(q)^(-1) times the sum over chi of the
twisted Gauss sum of conj chi times W2(beta, chi). Cauchy's inequality and Parseval
over the characters, which give phi(q)^2 for the Gauss sums, then bound
|S2 - S2*|^2 by the sum of |W2(beta, chi)|^2. W2 of page 5 is written out with chi
on the weight only, the form of A22Corr. -/
theorem char_orthogonality_18 (Y P : ℝ) (q a : ℕ) (hq : 1 ≤ q) (ha : Nat.Coprime a q)
    (hcop : ∀ m : ℕ, roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m ≠ 0 → Nat.Coprime m q)
    (β : ℝ) :
    ‖roughSum Y P ((a : ℝ) / q + β) - U1534.gaussS q a / (Nat.totient q : ℂ) * T2 Y P β‖ ^ 2 ≤
      ∑ χ : DirichletCharacter ℂ q,
        ‖∑ m ∈ squareWindow Y,
          (roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m * χ m -
            (if χ = 1 then ((Task556a.f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ)
             else 0)) * fourier ((m ^ 2 : ℕ) : ℤ) (β : AddCircle (1 : ℝ))‖ ^ 2 := by
  haveI : NeZero q := ⟨by omega⟩
  have hq0 : 0 < q := by omega
  have hφ : ((q.totient : ℂ)) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq0).ne'
  refine le_of_eq_of_le ?_ (cs_bound q a _)
  congr 1
  congr 1
  rw [eq_inv_mul_iff_mul_eq₀ hφ]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [per_m q a _ _ _ _ (hcop _)]
  rw [Finset.sum_sub_distrib, mul_sub, ← Finset.mul_sum, ← Finset.mul_sum]
  unfold roughSum T2
  congr 1
  · congr 1
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [fourier_split q a m hq0 β]
  · field_simp

/-! ## Display 15, arc localization, PROVED in burst-20261122 -/

theorem mem_arcPairs_bounds {P : ℝ} (hP : 0 ≤ P) {v : ℕ × ℕ} (hv : v ∈ arcPairs P) :
    1 ≤ v.1 ∧ (v.1 : ℝ) ≤ P ∧ v.2 ≤ v.1 ∧ Nat.Coprime v.2 v.1 := by
  unfold arcPairs at hv
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hv
  obtain ⟨⟨⟨h1, h2⟩, _⟩, h3, h4⟩ := hv
  refine ⟨h1, ?_, h3, h4⟩
  exact (Nat.cast_le.mpr h2).trans (Nat.floor_le hP)

theorem arc_disjoint {P R : ℝ} (hP : 0 ≤ P) (hR : 2 * P < R) {v w : ℕ × ℕ}
    (hv : v ∈ arcPairs P) (hw : w ∈ arcPairs P) {α : ℝ}
    (hav : α ∈ arc R v) (haw : α ∈ arc R w) : v = w := by
  obtain ⟨hv1, hvP, hv2, hvc⟩ := mem_arcPairs_bounds hP hv
  obtain ⟨hw1, hwP, hw2, hwc⟩ := mem_arcPairs_bounds hP hw
  unfold arc at hav haw
  simp only [Set.mem_ofPred_eq] at hav haw
  have hRpos : 0 < R := by linarith
  have key : |((w.1 * v.2 : ℕ) : ℝ) - ((v.1 * w.2 : ℕ) : ℝ)| < 1 := by
    have e : ((w.1 * v.2 : ℕ) : ℝ) - ((v.1 * w.2 : ℕ) : ℝ) =
        (v.1 : ℝ) * ((w.1 : ℝ) * α - w.2) - (w.1 : ℝ) * ((v.1 : ℝ) * α - v.2) := by
      push_cast; ring
    rw [e]
    calc _ ≤ |(v.1 : ℝ) * ((w.1 : ℝ) * α - w.2)| + |(w.1 : ℝ) * ((v.1 : ℝ) * α - v.2)| :=
          abs_sub _ _
      _ = (v.1 : ℝ) * |(w.1 : ℝ) * α - w.2| + (w.1 : ℝ) * |(v.1 : ℝ) * α - v.2| := by
          rw [abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]
      _ ≤ P * R⁻¹ + P * R⁻¹ := by
          gcongr
      _ = 2 * P / R := by ring
      _ < 1 := by rw [div_lt_one hRpos]; exact hR
  have heq : w.1 * v.2 = v.1 * w.2 := by
    have : ((w.1 * v.2 : ℕ) : ℤ) = ((v.1 * w.2 : ℕ) : ℤ) := by
      have h := key
      rw [← Int.cast_natCast (R := ℝ), ← Int.cast_natCast (R := ℝ) (v.1 * w.2), ← Int.cast_sub,
        ← Int.cast_abs] at h
      have h' : |((w.1 * v.2 : ℕ) : ℤ) - ((v.1 * w.2 : ℕ) : ℤ)| < 1 := by exact_mod_cast h
      have := abs_lt.mp h'
      omega
    exact_mod_cast this
  have h1 : v.1 ∣ w.1 := by
    have : v.1 ∣ v.2 * w.1 := ⟨w.2, by rw [mul_comm v.2, heq]⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left hvc.symm this)
  have h2 : w.1 ∣ v.1 := by
    have : w.1 ∣ w.2 * v.1 := ⟨v.2, by rw [heq]; ring⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left hwc.symm this)
  have hq : v.1 = w.1 := Nat.dvd_antisymm h1 h2
  have ha : v.2 = w.2 := by
    rw [hq] at heq
    exact Nat.eq_of_mul_eq_mul_left (by omega) heq
  exact Prod.ext hq ha

theorem cover {H P α : ℝ} (hP : 0 ≤ P) (hR : 1 < H / P) (hα : α ∈ Set.Ioc (0 : ℝ) 1)
    (hM : α ∈ majorArcs H P) : ∃ v ∈ arcPairs P, α ∈ arc (H / P) v := by
  obtain ⟨q, hq1, hqP, a, hcop, hab⟩ := hM
  have hinv : (H / P)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hR
  have hlt := (abs_lt.mp (lt_of_le_of_lt hab hinv))
  obtain ⟨hα0, hα1⟩ := hα
  have hqα : (q : ℝ) * α ≤ q := by
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    nlinarith
  have hqα0 : 0 < (q : ℝ) * α := mul_pos (by exact_mod_cast hq1) hα0
  have ha0 : (0 : ℤ) ≤ a := by
    have : (-1 : ℝ) < a := by linarith
    have : (-1 : ℤ) < a := by exact_mod_cast this
    omega
  have haq : a ≤ (q : ℤ) := by
    have : (a : ℝ) < q + 1 := by linarith
    have : a < (q : ℤ) + 1 := by exact_mod_cast this
    omega
  refine ⟨(q, a.toNat), ?_, ?_⟩
  · unfold arcPairs
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
    have hqf : q ≤ ⌊P⌋₊ := Nat.le_floor hqP
    refine ⟨⟨⟨hq1, hqf⟩, by omega⟩, by omega, ?_⟩
    have : IsCoprime ((a.toNat : ℕ) : ℤ) (q : ℤ) := by rwa [Int.toNat_of_nonneg ha0]
    exact Nat.isCoprime_iff_coprime.mp this
  · unfold arc
    simp only [Set.mem_ofPred_eq]
    have : ((a.toNat : ℕ) : ℝ) = (a : ℝ) := by
      have : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg ha0
      exact_mod_cast this
    rw [this]; exact hab

theorem S2star_on_arc {Y H P α : ℝ} (hP : 0 ≤ P) (hR : 2 * P < H / P) {v : ℕ × ℕ}
    (hv : v ∈ arcPairs P) (hα : α ∈ arc (H / P) v) :
    S2star Y H P α = U1534.gaussS v.1 v.2 / (Nat.totient v.1 : ℂ) *
      T2 Y P (α - v.2 / v.1) := by
  unfold S2star
  rw [Finset.sum_eq_single v]
  · rw [Set.indicator_of_mem hα]
  · intro w hw hwv
    rw [Set.indicator_of_notMem]
    intro hαw
    exact hwv (arc_disjoint hP hR hw hv hαw hα)
  · intro h; exact absurd hv h

theorem arc_eq_Icc {R : ℝ} (hR : 0 < R) {v : ℕ × ℕ} (hv : 1 ≤ v.1) :
    arc R v = Set.Icc ((v.2 : ℝ) / v.1 + -((v.1 : ℝ) * R)⁻¹) ((v.2 : ℝ) / v.1 + ((v.1 : ℝ) * R)⁻¹) := by
  have hq : (0 : ℝ) < v.1 := by exact_mod_cast hv
  ext α
  simp only [arc, Set.mem_ofPred_eq, Set.mem_Icc, abs_le]
  have key : ((v.1 : ℝ) * R)⁻¹ = R⁻¹ / v.1 := by rw [mul_inv]; ring
  rw [key]
  have e1 : (v.1 : ℝ) * α - v.2 = (α - v.2 / v.1) * v.1 := by field_simp
  rw [e1]
  generalize hd : α - v.2 / v.1 = d
  have hα : α = v.2 / v.1 + d := by rw [← hd]; ring
  rw [hα]
  constructor
  · rintro ⟨h1, h2⟩
    have a1 : -R⁻¹ / v.1 ≤ d := (div_le_iff₀ hq).mpr h1
    have a2 : d ≤ R⁻¹ / v.1 := (le_div_iff₀ hq).mpr h2
    rw [neg_div] at a1
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    have a1 : -R⁻¹ / v.1 ≤ d := by rw [neg_div]; linarith
    have a2 : d ≤ R⁻¹ / v.1 := by linarith
    exact ⟨(div_le_iff₀ hq).mp a1, (le_div_iff₀ hq).mp a2⟩

theorem arc_measurable (R : ℝ) (v : ℕ × ℕ) : MeasurableSet (arc R v) := by
  unfold arc
  exact measurableSet_le (by fun_prop) measurable_const

theorem cont_T2 (Y P : ℝ) : Continuous (fun β : ℝ => T2 Y P β) := by
  unfold T2
  exact Prep1121DKLMajorCut.trig_continuous _ _ _

theorem integral_bound {Y H P : ℝ} (hP : 0 ≤ P) (hR1 : 1 < H / P) (hR : 2 * P < H / P) :
    (∫ α in Set.Ioc (0 : ℝ) 1 ∩ majorArcs H P,
        ‖roughSum Y P α - S2star Y H P α‖ ^ 2) ≤
      ∑ v ∈ arcPairs P,
        ∫ β in -((v.1 : ℝ) * (H / P))⁻¹..((v.1 : ℝ) * (H / P))⁻¹,
          ‖roughSum Y P ((v.2 : ℝ) / v.1 + β) -
            U1534.gaussS v.1 v.2 / (Nat.totient v.1 : ℂ) * T2 Y P β‖ ^ 2 := by
  set R := H / P with hRdef
  have hRpos : 0 < R := by linarith
  set f : ℝ → ℝ := fun α => ‖roughSum Y P α - S2star Y H P α‖ ^ 2 with hf
  let g : ℕ × ℕ → ℝ → ℝ := fun v α =>
    ‖roughSum Y P α - U1534.gaussS v.1 v.2 / (Nat.totient v.1 : ℂ) * T2 Y P (α - v.2 / v.1)‖ ^ 2
  have hg : ∀ v, Continuous (g v) := fun v => by
    have h1 := Prep1121DKLMajorCut.cont_S2 Y P
    have h2 := cont_T2 Y P
    simp only [g]
    fun_prop
  have hfg : ∀ v ∈ arcPairs P, Set.EqOn f (g v) (arc R v) := by
    intro v hv α hα
    simp only [hf, g]
    rw [S2star_on_arc hP hR hv hα]
  have hint : ∀ v ∈ arcPairs P, IntegrableOn f (arc R v) := by
    intro v hv
    have h1 := (mem_arcPairs_bounds hP hv).1
    have : IntegrableOn (g v) (arc R v) := by
      rw [arc_eq_Icc hRpos h1]
      exact (hg v).integrableOn_Icc
    exact this.congr_fun (hfg v hv).symm (arc_measurable R v)
  have hdisj : Set.Pairwise (↑(arcPairs P)) (Function.onFun Disjoint fun v => arc R v) := by
    intro v hv w hw hvw
    rw [Function.onFun, Set.disjoint_left]
    intro α hαv hαw
    exact hvw (arc_disjoint hP hR hv hw hαv hαw)
  have hU : IntegrableOn f (⋃ v ∈ arcPairs P, arc R v) :=
    (integrableOn_finset_iUnion).mpr hint
  calc (∫ α in Set.Ioc (0 : ℝ) 1 ∩ majorArcs H P, f α)
      ≤ ∫ α in ⋃ v ∈ arcPairs P, arc R v, f α := by
        apply setIntegral_mono_set hU
        · exact Filter.Eventually.of_forall (fun α => by positivity)
        · apply Filter.Eventually.of_forall
          intro α hα
          obtain ⟨v, hv, hαv⟩ := cover hP hR1 hα.1 hα.2
          exact Set.mem_biUnion hv hαv
    _ = ∑ v ∈ arcPairs P, ∫ α in arc R v, f α :=
        integral_biUnion_finset _ (fun v _ => arc_measurable R v) hdisj hint
    _ = _ := by
        apply Finset.sum_congr rfl
        intro v hv
        have h1 := (mem_arcPairs_bounds hP hv).1
        rw [setIntegral_congr_fun (arc_measurable R v) (hfg v hv), arc_eq_Icc hRpos h1,
          integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le]
        · have e : ∀ β : ℝ, ‖roughSum Y P ((v.2 : ℝ) / v.1 + β) -
              U1534.gaussS v.1 v.2 / (Nat.totient v.1 : ℂ) * T2 Y P β‖ ^ 2 =
              g v ((v.2 : ℝ) / v.1 + β) := fun β => by simp only [g, add_sub_cancel_left]
          simp_rw [e]
          rw [intervalIntegral.integral_comp_add_left (g v) ((v.2 : ℝ) / v.1)]
        · have : 0 < ((v.1 : ℝ) * R)⁻¹ := inv_pos.mpr (mul_pos (by exact_mod_cast h1) hRpos)
          linarith

theorem eventually_big (B : ℝ) :
    ∀ᶠ X : ℝ in Filter.atTop, 1 ≤ X ∧ 1 ≤ Real.log X ∧
      2 * (Real.log X ^ B) ^ (6 : ℕ) < X ^ (7 / 18 : ℝ) := by
  have ht := (isLittleO_log_rpow_rpow_atTop (6 * B) (by norm_num : (0 : ℝ) < 7 / 18)).bound
    (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [ht, Filter.eventually_ge_atTop (Real.exp 1)] with X hsmall hX
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hL : 1 ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hLp : 0 < Real.log X := by linarith
  have hy : 0 < X ^ (7 / 18 : ℝ) := Real.rpow_pos_of_pos hX0 _
  have hsmall' : Real.log X ^ (6 * B) ≤ (1 / 4 : ℝ) * X ^ (7 / 18 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hLp (6 * B)),
      abs_of_pos hy] using hsmall
  refine ⟨le_trans (Real.one_le_exp zero_le_one) hX, hL, ?_⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul hLp.le]
  rw [show B * ((6 : ℕ) : ℝ) = 6 * B by push_cast; ring]
  linarith

/-- PROVED. P0088 page 4 display 15 and page 5 the definition of S2* on M. Was LEAF MEDIUM.
For X large in the block range, H/P exceeds 2P, so the closed arcs M(q, a) with q at
most P are disjoint, and every alpha of the period interval in M lies on the arc of
one pair of arcPairs P, with a from 0 to q. On that arc S2* is the single term
S(q, a)/phi(q) T2(alpha - a/q), and the substitution alpha = a/q + beta carries the
arc to |beta| at most 1/(qQ), Q = H/P. So the mean square over M is at most the sum
over the arcs of the mean squares in beta, the step from display 16 to display 19. -/
theorem arc_localization :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ X0 : ℝ, ∀ X H : ℝ, X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        (∫ α in Set.Ioc (0 : ℝ) 1 ∩ majorArcs H (Real.log X ^ B),
          ‖roughSum (windowY X ε) (Real.log X ^ B) α -
            S2star (windowY X ε) H (Real.log X ^ B) α‖ ^ 2) ≤
          ∑ v ∈ arcPairs (Real.log X ^ B),
            ∫ β in -((v.1 : ℝ) * (H / Real.log X ^ B))⁻¹..((v.1 : ℝ) * (H / Real.log X ^ B))⁻¹,
              ‖roughSum (windowY X ε) (Real.log X ^ B) ((v.2 : ℝ) / v.1 + β) -
                U1534.gaussS v.1 v.2 / (Nat.totient v.1 : ℂ) *
                  T2 (windowY X ε) (Real.log X ^ B) β‖ ^ 2 := by
  intro B hB ε hε _
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp (eventually_big B)
  refine ⟨X0, fun X H hX hH1 _ => ?_⟩
  obtain ⟨hX1, hL, hbig⟩ := hX0 X hX
  set P := Real.log X ^ B with hPdef
  have hLp : 0 < Real.log X := by linarith
  have hP1 : 1 ≤ P := Real.one_le_rpow hL hB.le
  have hPpos : 0 < P := by linarith
  have hXe : X ^ (7 / 18 : ℝ) ≤ X ^ (7 / 18 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hP4 : (0 : ℝ) < P ^ (4 : ℕ) := by positivity
  have hzp : P ^ (-4 : ℤ) = (P ^ (4 : ℕ))⁻¹ := by rw [zpow_neg, zpow_ofNat]
  have hH : 2 * P ^ (2 : ℕ) < H := by
    have h6 : 2 * P ^ (6 : ℕ) * (P ^ (4 : ℕ))⁻¹ = 2 * P ^ (2 : ℕ) := by
      field_simp
    calc 2 * P ^ (2 : ℕ) = 2 * P ^ (6 : ℕ) * (P ^ (4 : ℕ))⁻¹ := h6.symm
      _ < X ^ (7 / 18 : ℝ) * (P ^ (4 : ℕ))⁻¹ := by
          apply mul_lt_mul_of_pos_right hbig (inv_pos.mpr hP4)
      _ ≤ X ^ (7 / 18 + ε) * (P ^ (4 : ℕ))⁻¹ := by
          apply mul_le_mul_of_nonneg_right hXe (inv_pos.mpr hP4).le
      _ ≤ H := by rw [← hzp]; exact hH1
  have hR : 2 * P < H / P := by
    rw [lt_div_iff₀ hPpos]; nlinarith
  have hR1 : 1 < H / P := by linarith
  exact integral_bound hPpos.le hR1 hR

/-- LEAF: P0088 page 6, the display before display 20: Gallagher's lemma, reference 5
Lemma 1, combined with the device of Saffari and Vaughan, reference 21 page 25.
Class HARD, a citation wall: neither proof is printed in P0088. For each modulus q at
most P and each character chi modulo q there is delta of size qQ/Y, Q = H/P, at most
qQ/Y as (A2.2) requires, such that the integral of |W2(beta, chi)|^2 over |beta| at
most 1/(qQ) is at most a constant times (qQ)^(-2) times the mean square over
Y/4 < t <= Y of the sums of (A2.2), plus delta. The term delta carries the edge of
the t range below Y/4 and the bounded coefficients; the lower bound c qQ/Y keeps
delta of the printed size. -/
theorem gallagher_saffari_vaughan :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C c X0 : ℝ, 0 < C ∧ 0 < c ∧ ∀ X H : ℝ, X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
        ∀ χ : DirichletCharacter ℂ q,
          ∃ δ : ℝ, c * ((q : ℝ) * (H / Real.log X ^ B)) / windowY X ε ≤ δ ∧
            δ ≤ (q : ℝ) * (H / Real.log X ^ B) / windowY X ε ∧
            (∫ β in -((q : ℝ) * (H / Real.log X ^ B))⁻¹..((q : ℝ) * (H / Real.log X ^ B))⁻¹,
              ‖∑ m ∈ squareWindow (windowY X ε),
                (roughWeight (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) m * χ m -
                  (if χ = 1 then ((Task556a.f2Weight
                      (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ)
                   else 0)) * fourier ((m ^ 2 : ℕ) : ℤ) (β : AddCircle (1 : ℝ))‖ ^ 2) ≤
              C * (((q : ℝ) * (H / Real.log X ^ B)) ^ (-2 : ℤ) *
                (∫ t in windowY X ε / 4..windowY X ε,
                  ‖roughDefect χ (windowY X ε) (Real.log X ^ B) δ t‖ ^ 2) + δ) := by
  sorry

/-! ## Proved combinations -/

/-- PROVED from the LEAF gallagher_saffari_vaughan, CONDITIONAL ON A22Corr. P0088 page 6
before display 20: inserting (A2.2) into the Gallagher bound gives C P^(-4) for each
arc integral of |W2|^2, since (qQ)^(-2) (qQ)^2 = 1 and delta is at most qQ/Y, at most
H/Y, at most P^(-4) in the block range. No sorry of its own. -/
theorem arc_char_mean_square (h : A22Corr) :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ ∀ X H : ℝ, X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
        ∀ χ : DirichletCharacter ℂ q,
          (∫ β in -((q : ℝ) * (H / Real.log X ^ B))⁻¹..((q : ℝ) * (H / Real.log X ^ B))⁻¹,
              ‖∑ m ∈ squareWindow (windowY X ε),
                (roughWeight (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) m * χ m -
                  (if χ = 1 then ((Task556a.f2Weight
                      (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ)
                   else 0)) * fourier ((m ^ 2 : ℕ) : ℤ) (β : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * (Real.log X ^ B) ^ (-4 : ℤ) := by
  intro B hB ε hε hε'
  obtain ⟨C, c, X0, hC, hc, kG⟩ := gallagher_saffari_vaughan B hB ε hε hε'
  obtain ⟨CA, XA, hCA, kA⟩ := h B hB ε hε hε'
  refine ⟨C * (CA + 1), max (max X0 XA) 3, by positivity, ?_⟩
  intro X H hX hlo hhi q hq hqP χ
  have hX0 : X0 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXA : XA ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX3 : (3 : ℝ) ≤ X := le_trans (le_max_right _ _) hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hP : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hL B
  have hY : 0 < windowY X ε := Real.rpow_pos_of_pos (by linarith) _
  have hH : 0 < H := lt_of_lt_of_le (by
    have : 0 < X ^ (7 / 18 + ε) := Real.rpow_pos_of_pos (by linarith) _
    positivity) hlo
  set P := Real.log X ^ B with hPdef
  set Y := windowY X ε with hYdef
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hqQ : 0 < (q : ℝ) * (H / P) := by positivity
  obtain ⟨δ, hδ1, hδ2, hI⟩ := kG X H hX0 hlo hhi q hq hqP χ
  have hδ : 0 < δ := lt_of_lt_of_le (by positivity) hδ1
  have hA := kA X H hXA hlo hhi q hq hqP χ δ hδ hδ2
  have hP4 : 0 < P ^ (-4 : ℤ) := zpow_pos hP _
  have hδP : δ ≤ P ^ (-4 : ℤ) := by
    have h1 : (q : ℝ) * (H / P) ≤ H := by
      calc (q : ℝ) * (H / P) ≤ P * (H / P) :=
            mul_le_mul_of_nonneg_right hqP (by positivity)
        _ = H := by field_simp
    have h2 : H / Y ≤ P ^ (-4 : ℤ) := by
      rw [div_le_iff₀ hY]; linarith
    calc δ ≤ (q : ℝ) * (H / P) / Y := hδ2
      _ ≤ H / Y := div_le_div_of_nonneg_right h1 hY.le
      _ ≤ P ^ (-4 : ℤ) := h2
  have hz : 0 ≤ ((q : ℝ) * (H / P)) ^ (-2 : ℤ) := (zpow_pos hqQ _).le
  have hone : ((q : ℝ) * (H / P)) ^ (-2 : ℤ) * ((q : ℝ) * (H / P)) ^ 2 = 1 := by
    rw [zpow_neg, zpow_two, sq]
    field_simp
  calc _ ≤ C * (((q : ℝ) * (H / P)) ^ (-2 : ℤ) *
          (∫ t in Y / 4..Y, ‖roughDefect χ Y P δ t‖ ^ 2) + δ) := hI
    _ ≤ C * (((q : ℝ) * (H / P)) ^ (-2 : ℤ) *
          (CA * ((q : ℝ) * (H / P)) ^ 2 * P ^ (-4 : ℤ)) + P ^ (-4 : ℤ)) := by
        gcongr
    _ = C * (CA + 1) * P ^ (-4 : ℤ) := by
        rw [show ((q : ℝ) * (H / P)) ^ (-2 : ℤ) * (CA * ((q : ℝ) * (H / P)) ^ 2 * P ^ (-4 : ℤ))
            = CA * P ^ (-4 : ℤ) * (((q : ℝ) * (H / P)) ^ (-2 : ℤ) * ((q : ℝ) * (H / P)) ^ 2)
            by ring, hone]
        ring

/-- PROVED. The arcs of arcPairs P number at most 2 P^2 when P is at least one:
q runs over 1 to the floor of P and a over 0 to the floor of P. -/
theorem card_arcPairs_le {P : ℝ} (hP : 1 ≤ P) : ((arcPairs P).card : ℝ) ≤ 2 * P ^ 2 := by
  have hc : (arcPairs P).card ≤ ⌊P⌋₊ * (⌊P⌋₊ + 1) := by
    unfold arcPairs
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Finset.card_product, Nat.card_Icc, Finset.card_range, Nat.add_sub_cancel]
  have hf : (⌊P⌋₊ : ℝ) ≤ P := Nat.floor_le (by linarith)
  have hf0 : (0 : ℝ) ≤ ⌊P⌋₊ := Nat.cast_nonneg _
  calc ((arcPairs P).card : ℝ) ≤ ((⌊P⌋₊ * (⌊P⌋₊ + 1) : ℕ) : ℝ) := by exact_mod_cast hc
    _ = (⌊P⌋₊ : ℝ) * ((⌊P⌋₊ : ℝ) + 1) := by push_cast; ring
    _ ≤ P * (P + P) := by gcongr
    _ = 2 * P ^ 2 := by ring

/-- The exact statement of Prep1121DKLMajorCut.S2_sub_S2star_major_mean_square, P0088
page 5 displays 18, 19 and page 6 display 20, from the LEAF pieces arc_localization,
char_orthogonality_18 and gallagher_saffari_vaughan, CONDITIONAL ON A22Corr.
The coprimality (A2.1) for X large is Task556a.roughWeight_eventually_coprime, PROVED.
Each arc gives at most phi(q) C P^(-4), at most C P^(-3); at most 2 P^2 arcs give
2 C P^(-1), at most 2 C P^(-1/2). No sorry of its own. -/
theorem S2_sub_S2star_major_mean_square_of_pieces (h : A22Corr) :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ ∀ X H : ℝ, X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        (∫ α in Set.Ioc (0 : ℝ) 1 ∩ majorArcs H (Real.log X ^ B),
          ‖roughSum (windowY X ε) (Real.log X ^ B) α -
            S2star (windowY X ε) H (Real.log X ^ B) α‖ ^ 2) ≤
            C * (Real.log X ^ B) ^ (-(1 / 2 : ℝ)) := by
  intro B hB ε hε hε'
  obtain ⟨C1, X1, hC1, k1⟩ := arc_char_mean_square h B hB ε hε hε'
  obtain ⟨X2, k2⟩ := arc_localization B hB ε hε hε'
  obtain ⟨X3, k3⟩ := Filter.eventually_atTop.mp (roughWeight_eventually_coprime B ε hε)
  refine ⟨2 * C1, max (max X1 X2) (max X3 3), by positivity, ?_⟩
  intro X H hX hlo hhi
  have hX1 : X1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX2 : X2 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX3 : X3 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hX3' : (3 : ℝ) ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hP1 : 1 ≤ Real.log X ^ B := Real.one_le_rpow hL1 hB.le
  have hcopX := k3 X hX3
  set P := Real.log X ^ B with hPdef
  set Y := windowY X ε with hYdef
  have hP0 : 0 < P := by linarith
  have hP4 : 0 < P ^ (-4 : ℤ) := zpow_pos hP0 _
  have hH : 0 < H := lt_of_lt_of_le (by
    have : 0 < X ^ (7 / 18 + ε) := Real.rpow_pos_of_pos (by linarith) _
    positivity) hlo
  have harc : ∀ v ∈ arcPairs P,
      (∫ β in -((v.1 : ℝ) * (H / P))⁻¹..((v.1 : ℝ) * (H / P))⁻¹,
        ‖roughSum Y P ((v.2 : ℝ) / v.1 + β) -
          U1534.gaussS v.1 v.2 / (Nat.totient v.1 : ℂ) * T2 Y P β‖ ^ 2) ≤
        P * (C1 * P ^ (-4 : ℤ)) := by
    intro v hv
    obtain ⟨hvp, -, hcop⟩ := Finset.mem_filter.mp hv
    have hq := (Finset.mem_Icc.mp (Finset.mem_product.mp hvp).1)
    have hq1 : 1 ≤ v.1 := hq.1
    have hqP : (v.1 : ℝ) ≤ P := (Nat.cast_le.mpr hq.2).trans (Nat.floor_le hP0.le)
    have : NeZero v.1 := ⟨by omega⟩
    have hr : -((v.1 : ℝ) * (H / P))⁻¹ ≤ ((v.1 : ℝ) * (H / P))⁻¹ := by
      have : 0 ≤ ((v.1 : ℝ) * (H / P))⁻¹ := by positivity
      linarith
    have hW : ∀ χ : DirichletCharacter ℂ v.1, Continuous (fun β : ℝ =>
        ‖∑ m ∈ squareWindow Y,
          (roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m * χ m -
            (if χ = 1 then ((Task556a.f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ)
             else 0)) * fourier ((m ^ 2 : ℕ) : ℤ) (β : AddCircle (1 : ℝ))‖ ^ 2) := fun χ =>
      (Prep1121DKLMajorCut.trig_continuous _ _ (fun m => ((m ^ 2 : ℕ) : ℤ))).norm.pow 2
    have hT2 : Continuous (fun β : ℝ => T2 Y P β) := by
      unfold T2
      exact Prep1121DKLMajorCut.trig_continuous _ _ (fun m => ((m ^ 2 : ℕ) : ℤ))
    have hL : Continuous (fun β : ℝ => ‖roughSum Y P ((v.2 : ℝ) / v.1 + β) -
          U1534.gaussS v.1 v.2 / (Nat.totient v.1 : ℂ) * T2 Y P β‖ ^ 2) :=
      (((Prep1121DKLMajorCut.cont_S2 Y P).comp (continuous_const.add continuous_id)).sub
        (continuous_const.mul hT2)).norm.pow 2
    have hcard : (Finset.univ : Finset (DirichletCharacter ℂ v.1)).card = Nat.totient v.1 := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ v.1
    have htot : ((Nat.totient v.1 : ℕ) : ℝ) ≤ P :=
      (Nat.cast_le.mpr (Nat.totient_le v.1)).trans hqP
    calc _ ≤ ∫ β in -((v.1 : ℝ) * (H / P))⁻¹..((v.1 : ℝ) * (H / P))⁻¹,
          ∑ χ : DirichletCharacter ℂ v.1,
            ‖∑ m ∈ squareWindow Y,
              (roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m * χ m -
                (if χ = 1 then ((Task556a.f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ)
                 else 0)) * fourier ((m ^ 2 : ℕ) : ℤ) (β : AddCircle (1 : ℝ))‖ ^ 2 := by
          refine intervalIntegral.integral_mono_on hr (hL.intervalIntegrable _ _)
            ((continuous_finsetSum _ fun χ _ => hW χ).intervalIntegrable _ _) ?_
          intro β _
          exact char_orthogonality_18 Y P v.1 v.2 hq1 hcop
            (fun m hm => hcopX v.1 (by omega) hqP m hm) β
      _ = ∑ χ : DirichletCharacter ℂ v.1, ∫ β in -((v.1 : ℝ) * (H / P))⁻¹..((v.1 : ℝ) * (H / P))⁻¹,
            ‖∑ m ∈ squareWindow Y,
              (roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m * χ m -
                (if χ = 1 then ((Task556a.f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ)
                 else 0)) * fourier ((m ^ 2 : ℕ) : ℤ) (β : AddCircle (1 : ℝ))‖ ^ 2 :=
          intervalIntegral.integral_finsetSum fun χ _ => (hW χ).intervalIntegrable _ _
      _ ≤ ∑ _χ : DirichletCharacter ℂ v.1, C1 * P ^ (-4 : ℤ) :=
          Finset.sum_le_sum fun χ _ => k1 X H hX1 hlo hhi v.1 hq1 hqP χ
      _ = (Nat.totient v.1 : ℝ) * (C1 * P ^ (-4 : ℤ)) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
      _ ≤ P * (C1 * P ^ (-4 : ℤ)) := by gcongr
  have hcardA := card_arcPairs_le hP1
  calc _ ≤ _ := k2 X H hX2 hlo hhi
    _ ≤ ∑ _v ∈ arcPairs P, P * (C1 * P ^ (-4 : ℤ)) := Finset.sum_le_sum harc
    _ = ((arcPairs P).card : ℝ) * (P * (C1 * P ^ (-4 : ℤ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * P ^ 2) * (P * (C1 * P ^ (-4 : ℤ))) := by gcongr
    _ = 2 * C1 * P ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one, zpow_neg]
        field_simp
    _ ≤ 2 * C1 * P ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP1 (by norm_num))
          (by positivity)

example : type_of% @Prep1121DKLMajorCut.S2_sub_S2star_major_mean_square :=
  S2_sub_S2star_major_mean_square_of_pieces

end LeanLab.KumchevLiu2007.Prep1122KLGallagherCut

#print axioms LeanLab.KumchevLiu2007.Prep1122KLGallagherCut.char_orthogonality_18
#print axioms LeanLab.KumchevLiu2007.Prep1122KLGallagherCut.arc_localization
#print axioms LeanLab.KumchevLiu2007.Prep1122KLGallagherCut.gallagher_saffari_vaughan
#print axioms LeanLab.KumchevLiu2007.Prep1122KLGallagherCut.arc_char_mean_square
#print axioms LeanLab.KumchevLiu2007.Prep1122KLGallagherCut.card_arcPairs_le
#print axioms LeanLab.KumchevLiu2007.Prep1122KLGallagherCut.S2_sub_S2star_major_mean_square_of_pieces
