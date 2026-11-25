import LeanLab.Halupczok2012.TotientSum398c
import LeanLab.Halupczok2012.Induced398c
import LeanLab.Halupczok2012.CharExpansion398c

/-!
Toward the LEAF `display4_reduction` of Resplit398c, PPS1984 page 531 display 4,
the reduction of the modulus sum to primitive characters.
Source: Perelli, Pintz, Salerno, Bombieri's theorem in short intervals,
Ann. Sc. Norm. Sup. Pisa 11, 1984, pages 529 to 539, copy papers/PPS1984.pdf.

This file proves intermediate steps of display 4 from the first three displays of
page 531, which are proved in CharExpansion398c, Induced398c and TotientSum398c.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Resplit398c

open Finset
open scoped Classical ArithmeticFunction.vonMangoldt

/-- PPS1984 page 531 display 4, first step, one modulus: each `χ` mod `q` is replaced by its
primitive character `χ₁` at cost `log₂ q · log (z + h)`, and there are `φ(q)` characters, so
`ppsTerm z h q a ≤ 1/φ(q) ∑_χ ‖E(z, h, χ₁)‖ + log₂ q · log (z + h)`. -/
theorem ppsTerm_le_primitive {q : ℕ} (hq : 1 ≤ q) {a : ℤ} (ha : Int.gcd a q = 1)
    {z h : ℝ} (hz : 1 ≤ z) (hh : 0 ≤ h) :
    ppsTerm z h q a ≤ (1 / (q.totient : ℝ)) *
        ∑ χ : DirichletCharacter ℂ q, ‖charE z h χ.primitiveCharacter‖ +
      Real.logb 2 q * Real.log (z + h) := by
  have : NeZero q := ⟨by omega⟩
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hcard : (Fintype.card (DirichletCharacter ℂ q) : ℝ) = q.totient := by
    rw [← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q]
  refine (ppsTerm_le_sum_norm_charE hq ha hh).trans ?_
  have hpt : ∀ χ : DirichletCharacter ℂ q, ‖charE z h χ‖ ≤
      ‖charE z h χ.primitiveCharacter‖ + Real.logb 2 q * Real.log (z + h) := by
    intro χ
    have := induced_bound hq χ hz hh
    have h2 := norm_sub_norm_le (charE z h χ) (charE z h χ.primitiveCharacter)
    rw [norm_sub_rev] at this
    linarith
  calc (1 / (q.totient : ℝ)) * ∑ χ : DirichletCharacter ℂ q, ‖charE z h χ‖
      ≤ (1 / (q.totient : ℝ)) * ∑ χ : DirichletCharacter ℂ q,
          (‖charE z h χ.primitiveCharacter‖ + Real.logb 2 q * Real.log (z + h)) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun χ _ => hpt χ) (by positivity)
    _ = _ := by
        rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, hcard, mul_add]
        congr 1
        field_simp

/-- PPS1984 page 531 display 4, regrouping step: for a fixed modulus `q`, the character `χ`
is determined by its primitive character, viewed in the sigma type over conductors. -/
theorem primitiveCharacter_sigma_injective (q : ℕ) :
    Function.Injective (fun χ : DirichletCharacter ℂ q =>
      (⟨χ.conductor, χ.primitiveCharacter⟩ : Σ n : ℕ, DirichletCharacter ℂ n)) := by
  have key : ∀ (s t : Σ n : ℕ, DirichletCharacter ℂ n) (hs : s.1 ∣ q) (ht : t.1 ∣ q),
      s = t → DirichletCharacter.changeLevel hs s.2 = DirichletCharacter.changeLevel ht t.2 := by
    rintro s _ _ _ rfl; rfl
  intro χ ψ hχψ
  rw [← χ.changeLevel_primitiveCharacter, ← ψ.changeLevel_primitiveCharacter]
  exact key ⟨χ.conductor, χ.primitiveCharacter⟩ ⟨ψ.conductor, ψ.primitiveCharacter⟩
    χ.conductor_dvd_level ψ.conductor_dvd_level hχψ

/-- PPS1984 page 531 display 4, regrouping step: the characters `χ` mod `q ≤ N` are grouped by
their primitive characters `χ₁` mod `q₁`; since `χ₁` determines `χ` for fixed `q` and `q₁ ∣ q`,
`∑_q w q ∑_{χ mod q} f χ₁ ≤ ∑_{q₁ ≤ N} ∑_{χ₁ primitive mod q₁} f χ₁ ∑_{q ≤ N, q₁ ∣ q} w q`
for nonnegative `w` and `f`. -/
theorem regroup_primitive (N : ℕ) (w : ℕ → ℝ) (hw : ∀ q, 0 ≤ w q)
    (f : (Σ n : ℕ, DirichletCharacter ℂ n) → ℝ) (hf : ∀ s, 0 ≤ f s) :
    ∑ q ∈ Icc 1 N, w q * ∑ χ : DirichletCharacter ℂ q, f ⟨χ.conductor, χ.primitiveCharacter⟩ ≤
      ∑ s ∈ (Icc 1 N).sigma (fun n => (univ : Finset (DirichletCharacter ℂ n)).filter
          (fun χ => χ.IsPrimitive)),
        f s * ∑ q ∈ (Icc 1 N).filter (s.1 ∣ ·), w q := by
  set S := (Icc 1 N).sigma (fun n => (univ : Finset (DirichletCharacter ℂ n)).filter
          (fun χ => χ.IsPrimitive)) with hS
  have hstep : ∀ q ∈ Icc 1 N, w q * ∑ χ : DirichletCharacter ℂ q,
      f ⟨χ.conductor, χ.primitiveCharacter⟩ ≤ w q * ∑ s ∈ S.filter (fun s => s.1 ∣ q), f s := by
    intro q hq
    have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
    have hqN : q ≤ N := (mem_Icc.mp hq).2
    apply mul_le_mul_of_nonneg_left _ (hw q)
    rw [← sum_image (f := f) (fun a _ b _ hab => primitiveCharacter_sigma_injective q hab)]
    apply sum_le_sum_of_subset_of_nonneg _ (fun s _ _ => hf s)
    intro s hs
    obtain ⟨χ, _, rfl⟩ := mem_image.mp hs
    have hd : χ.conductor ∣ q := χ.conductor_dvd_level
    have hpos : 0 < χ.conductor := Nat.pos_of_dvd_of_pos hd (by omega)
    simp only [hS, mem_filter, mem_sigma, mem_Icc, mem_univ, true_and]
    exact ⟨⟨⟨hpos, (Nat.le_of_dvd (by omega) hd).trans hqN⟩,
      DirichletCharacter.primitiveCharacter_isPrimitive χ⟩, hd⟩
  refine (sum_le_sum hstep).trans (le_of_eq ?_)
  simp only [mul_sum, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun s _ => sum_congr rfl fun q _ => ?_
  split_ifs <;> ring

/-- A totient lower bound used in the dyadic step of PPS1984 page 531 display 4:
`n / φ(n) ≤ Kc (1/4) (1 + log n)`. Route: `n = ∑_{d ∣ n} φ(d)` and `φ(d) φ(n/d) ≤ φ(n)`,
so `n / φ(n) ≤ ∑_{e ∣ n} 1/φ(e) ≤ ∑_{e ≤ n} 1/φ(e)`. -/
theorem self_div_totient_le {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) / n.totient ≤ Kc (1 / 4) * (1 + Real.log n) := by
  have hφ : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hsum : (n : ℝ) = ∑ d ∈ n.divisors, (d.totient : ℝ) := by
    exact_mod_cast (Nat.sum_totient n).symm
  refine le_trans ?_ (sum_inv_totient_le n)
  rw [hsum, sum_div]
  calc ∑ d ∈ n.divisors, (d.totient : ℝ) / n.totient
      ≤ ∑ d ∈ n.divisors, 1 / ((n / d).totient : ℝ) := by
        apply sum_le_sum
        intro d hd
        have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
        have hnd : 0 < n / d := Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)
        have hφ2 : (0 : ℝ) < (n / d).totient := by exact_mod_cast Nat.totient_pos.mpr hnd
        have hsup : (d.totient : ℝ) * (n / d).totient ≤ n.totient := by
          have := Nat.totient_super_multiplicative d (n / d)
          rw [Nat.mul_div_cancel' hdn] at this
          exact_mod_cast this
        rw [div_le_div_iff₀ hφ hφ2]
        linarith
    _ = ∑ e ∈ n.divisors, 1 / (e.totient : ℝ) :=
        Nat.sum_div_divisors n (fun e => 1 / (e.totient : ℝ))
    _ ≤ ∑ e ∈ Icc 1 n, 1 / (e.totient : ℝ) := by
        apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
        intro e he
        exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors he, Nat.divisor_le he⟩

/-- Every `1 ≤ n ≤ ⌊Q⌋` lies in a dyadic block `Q/2^(j+1) < n ≤ Q/2^j` with
`j ≤ log₂ ⌊Q⌋`. Helper for the dyadic step of PPS1984 page 531 display 4. -/
theorem exists_dyadic_block {Q : ℝ} (hQ : 1 ≤ Q) {n : ℕ} (hn : n ∈ Icc 1 ⌊Q⌋₊) :
    ∃ j ∈ range (Nat.log 2 ⌊Q⌋₊ + 1),
      n ∈ (Icc 1 ⌊Q / 2 ^ j⌋₊).filter (fun k : ℕ => Q / 2 ^ j / 2 < (k : ℝ)) := by
  obtain ⟨hn1, hnm⟩ := mem_Icc.mp hn
  set m := ⌊Q⌋₊ with hm
  have hQ0 : (0 : ℝ) ≤ Q := by linarith
  set j := Nat.log 2 (m / n) with hj
  have hmn : m / n ≠ 0 := (Nat.div_pos hnm (by omega)).ne'
  have h1 : 2 ^ j ≤ m / n := Nat.pow_log_le_self 2 hmn
  have h2 : m / n < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h3 : n * 2 ^ j ≤ m :=
    (Nat.mul_le_mul_left n h1).trans (Nat.mul_div_le m n)
  have h4 : m < n * 2 ^ (j + 1) := by
    rw [Nat.div_lt_iff_lt_mul (by omega)] at h2; linarith
  refine ⟨j, ?_, ?_⟩
  · rw [mem_range, Nat.lt_succ_iff]
    exact Nat.log_mono_right (Nat.div_le_self m n)
  have hpow : (0 : ℝ) < 2 ^ j := by positivity
  simp only [mem_filter, mem_Icc]
  refine ⟨⟨hn1, ?_⟩, ?_⟩
  · rw [Nat.le_floor_iff (by positivity), le_div_iff₀ hpow]
    have : ((n * 2 ^ j : ℕ) : ℝ) ≤ Q := (Nat.cast_le.mpr h3).trans (Nat.floor_le hQ0)
    exact_mod_cast this
  · have : Q < ((n * 2 ^ (j + 1) : ℕ) : ℝ) := (Nat.floor_lt hQ0).mp h4
    push_cast at this
    rw [div_div, div_lt_iff₀ (by positivity)]
    calc Q < n * 2 ^ (j + 1) := this
      _ = n * (2 ^ j * 2) := by ring

/-- PPS1984 page 531 display 4, dyadic step: for nonnegative `P`, some dyadic block
`Q'/2 < n ≤ Q'` with `1 ≤ Q' ≤ Q` carries the sum of `P n / n` over `n ≤ Q`, up to the factor
`2 (log₂ Q + 1) / Q'`. -/
theorem dyadic_pigeonhole (P : ℕ → ℝ) (hP : ∀ n, 0 ≤ P n) {Q : ℝ} (hQ : 1 ≤ Q) :
    ∃ Q' : ℝ, 1 ≤ Q' ∧ Q' ≤ Q ∧
      ∑ n ∈ Icc 1 ⌊Q⌋₊, P n / n ≤
        2 * ((Nat.log 2 ⌊Q⌋₊ : ℝ) + 1) / Q' *
          ∑ n ∈ (Icc 1 ⌊Q'⌋₊).filter (fun k : ℕ => Q' / 2 < (k : ℝ)), P n := by
  set J := Nat.log 2 ⌊Q⌋₊ with hJ
  set B : ℕ → Finset ℕ := fun j =>
    (Icc 1 ⌊Q / 2 ^ j⌋₊).filter (fun k : ℕ => Q / 2 ^ j / 2 < (k : ℝ)) with hB
  set F : ℕ → ℝ := fun j => 2 / (Q / 2 ^ j) * ∑ n ∈ B j, P n with hF
  have hQ0 : (0 : ℝ) < Q := by linarith
  -- each block level `Q / 2^j` is at least `1`
  have hlev : ∀ j ∈ range (J + 1), 1 ≤ Q / 2 ^ j := by
    intro j hj
    have hjJ : j ≤ J := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hm1 : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by exact_mod_cast hQ)
    have h2j : 2 ^ j ≤ ⌊Q⌋₊ :=
      (Nat.pow_le_pow_right (by norm_num) hjJ).trans (Nat.pow_log_le_self 2 (by omega))
    have : ((2 ^ j : ℕ) : ℝ) ≤ Q := (Nat.cast_le.mpr h2j).trans (Nat.floor_le hQ0.le)
    push_cast at this
    rw [le_div_iff₀ (by positivity), one_mul]; exact this
  obtain ⟨j0, hj0, hmax⟩ := exists_max_image (range (J + 1)) F ⟨0, by simp⟩
  refine ⟨Q / 2 ^ j0, hlev j0 hj0, div_le_self hQ0.le (one_le_pow₀ (by norm_num)), ?_⟩
  have hterm : ∀ n, 0 ≤ P n / n := fun n => div_nonneg (hP n) (Nat.cast_nonneg n)
  -- covering by blocks
  have hcover : ∑ n ∈ Icc 1 ⌊Q⌋₊, P n / n ≤
      ∑ j ∈ range (J + 1), ∑ n ∈ B j, P n / n := by
    calc ∑ n ∈ Icc 1 ⌊Q⌋₊, P n / n
        ≤ ∑ n ∈ Icc 1 ⌊Q⌋₊, ∑ j ∈ range (J + 1), if n ∈ B j then P n / n else 0 := by
          apply sum_le_sum
          intro n hn
          obtain ⟨j, hj, hnj⟩ := exists_dyadic_block hQ hn
          have := single_le_sum (f := fun j => if n ∈ B j then P n / n else 0)
            (fun i _ => by split_ifs; exacts [hterm n, le_rfl]) hj
          simpa only [show n ∈ B j from hnj, ↓reduceIte] using this
      _ = ∑ j ∈ range (J + 1), ∑ n ∈ (Icc 1 ⌊Q⌋₊).filter (· ∈ B j), P n / n := by
          rw [sum_comm]; simp only [sum_filter]
      _ ≤ ∑ j ∈ range (J + 1), ∑ n ∈ B j, P n / n := by
          apply sum_le_sum; intro j _
          apply sum_le_sum_of_subset_of_nonneg _ (fun n _ _ => hterm n)
          intro n hn; exact (mem_filter.mp hn).2
  -- on block `j`, `1/n ≤ 2 / (Q/2^j)`
  have hblock : ∀ j ∈ range (J + 1), ∑ n ∈ B j, P n / n ≤ F j := by
    intro j hj
    have hl := hlev j hj
    simp only [hF, mul_sum]
    apply sum_le_sum
    intro n hn
    have hn2 : Q / 2 ^ j / 2 < (n : ℝ) := (mem_filter.mp hn).2
    have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn2
    rw [div_eq_mul_inv, mul_comm (2 / (Q / 2 ^ j))]
    apply mul_le_mul_of_nonneg_left _ (hP n)
    rw [inv_le_comm₀ hnpos (by positivity), inv_div]
    linarith
  calc ∑ n ∈ Icc 1 ⌊Q⌋₊, P n / n ≤ ∑ j ∈ range (J + 1), F j :=
        hcover.trans (sum_le_sum hblock)
    _ ≤ ∑ j ∈ range (J + 1), F j0 := sum_le_sum fun j hj => hmax j hj
    _ = ((J : ℝ) + 1) * F j0 := by
        rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
    _ = _ := by simp only [hF, hB]; ring

/-- PPS1984 page 531 display 4, reduction to primitive characters: the statement of
`Resplit398c.display4_reduction`, copied verbatim, with `c = 3` and `C = 24 Kc(1/4)^2`.
Steps: `ppsTerm_le_primitive` for each modulus, a choice of maximizing `h'`, `z'` for each
primitive character, `regroup_primitive`, the third display through
`sum_multiples_inv_totient_le`, `self_div_totient_le`, and `dyadic_pigeonhole`. -/
theorem display4_reduction_proved :
    ∃ c : ℝ, 0 < c ∧ ∃ C x0 : ℝ, ∀ x y Q : ℝ, x0 ≤ x → 0 < y → y ≤ x → 1 ≤ Q → Q ≤ x →
      ∀ (a : ℕ → ℤ) (h z : ℕ → ℝ), (∀ q, Int.gcd (a q) q = 1) →
      (∀ q, 0 < h q ∧ h q ≤ y) → (∀ q, x / 2 < z q ∧ z q ≤ x) →
      ∃ Q' : ℝ, 1 ≤ Q' ∧ Q' ≤ Q ∧ ∃ h' z' : (q : ℕ) → DirichletCharacter ℂ q → ℝ,
        (∀ q χ, 0 < h' q χ ∧ h' q χ ≤ y) ∧ (∀ q χ, x / 2 < z' q χ ∧ z' q χ ≤ x) ∧
        ∑ q ∈ Icc 1 ⌊Q⌋₊, ppsTerm (z q) (h q) q (a q) ≤
          C * (Real.log x ^ c / Q' * primSum Q' h' z') + C * Q * Real.log x ^ 3 := by
  refine ⟨3, by norm_num, 24 * Kc (1 / 4) ^ 2, 3, ?_⟩
  intro x y Q hx _hy0 _hyx hQ1 hQx a h z hag hh hz
  set N := ⌊Q⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hQ1)
  have hxpos : 0 < x := by linarith
  have hL1 : 1 ≤ Real.log x := one_le_log_of_three_le hx
  have hK1 : 1 ≤ Kc (1 / 4) := one_le_Kc _
  have hK0 : 0 ≤ Kc (1 / 4) := by linarith
  have hNQ : (N : ℝ) ≤ Q := Nat.floor_le (by linarith)
  have hNx : (N : ℝ) ≤ x := hNQ.trans hQx
  have hne : (Icc 1 N).Nonempty := ⟨1, mem_Icc.mpr ⟨le_rfl, hN1⟩⟩
  have hsel : ∀ s : (Σ n : ℕ, DirichletCharacter ℂ n), ∃ q0 ∈ Icc 1 N, ∀ q ∈ Icc 1 N,
      ‖charE (z q) (h q) s.2‖ ≤ ‖charE (z q0) (h q0) s.2‖ :=
    fun s => exists_max_image _ _ hne
  choose q0 _hq0 hq0max using hsel
  set h' : (q : ℕ) → DirichletCharacter ℂ q → ℝ := fun n χ => h (q0 ⟨n, χ⟩) with hh'
  set z' : (q : ℕ) → DirichletCharacter ℂ q → ℝ := fun n χ => z (q0 ⟨n, χ⟩) with hz'
  set G : (Σ n : ℕ, DirichletCharacter ℂ n) → ℝ :=
    fun s => ‖charE (z' s.1 s.2) (h' s.1 s.2) s.2‖ with hG
  set P : ℕ → ℝ := fun n => ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ n)).filter
    (fun χ => χ.IsPrimitive), G ⟨n, χ⟩ with hP
  have hP0 : ∀ n, 0 ≤ P n := fun n => sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨Q', hQ'1, hQ'Q, hdy⟩ := dyadic_pigeonhole P hP0 hQ1
  refine ⟨Q', hQ'1, hQ'Q, h', z', fun q χ => hh _, fun q χ => hz _, ?_⟩
  have hprim : primSum Q' h' z' =
      ∑ n ∈ (Icc 1 ⌊Q'⌋₊).filter (fun k : ℕ => Q' / 2 < (k : ℝ)), P n := rfl
  rw [← hprim] at hdy
  have hPS := primSum_nonneg Q' h' z'
  -- one modulus
  have hA : ∀ q ∈ Icc 1 N, ppsTerm (z q) (h q) q (a q) ≤ (1 / (q.totient : ℝ)) *
      ∑ χ : DirichletCharacter ℂ q, G ⟨χ.conductor, χ.primitiveCharacter⟩ +
        4 * Real.log x ^ 3 := by
    intro q hq
    have hq1 := (mem_Icc.mp hq).1
    have hqx : (q : ℝ) ≤ x := (Nat.cast_le.mpr (mem_Icc.mp hq).2).trans hNx
    obtain ⟨hz1, hz2⟩ := hz q
    obtain ⟨hh1, hh2⟩ := hh q
    refine (ppsTerm_le_primitive hq1 (hag q) (by linarith) hh1.le).trans (add_le_add ?_ ?_)
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum
      intro χ _
      exact hq0max ⟨χ.conductor, χ.primitiveCharacter⟩ q hq
    · have hl2 := Real.log_two_gt_d9
      have hl2' := Real.log_two_lt_d9
      have hlq : Real.log q ≤ Real.log x := Real.log_le_log (by exact_mod_cast hq1) hqx
      have hlq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
      have hlb : Real.logb 2 q ≤ 2 * Real.log x := by
        rw [Real.logb, div_le_iff₀ (Real.log_pos one_lt_two)]
        nlinarith
      have hlz : Real.log (z q + h q) ≤ 2 * Real.log x := by
        have := Real.log_le_log (by linarith) (show z q + h q ≤ 2 * x by linarith)
        rw [Real.log_mul two_ne_zero hxpos.ne'] at this
        linarith
      have h0' : 0 ≤ Real.log (z q + h q) := Real.log_nonneg (by linarith)
      calc Real.logb 2 q * Real.log (z q + h q) ≤ (2 * Real.log x) * (2 * Real.log x) :=
            mul_le_mul hlb hlz h0' (by linarith)
        _ ≤ 4 * Real.log x ^ 3 := by nlinarith
  -- regrouping and the third display
  have hC : ∑ q ∈ Icc 1 N, (1 / (q.totient : ℝ)) *
      ∑ χ : DirichletCharacter ℂ q, G ⟨χ.conductor, χ.primitiveCharacter⟩ ≤
        Kc (1 / 4) * (2 * Real.log x) * ∑ n ∈ Icc 1 N, P n / n.totient := by
    refine (regroup_primitive N (fun q => 1 / (q.totient : ℝ)) (fun q => by positivity) G
      (fun s => norm_nonneg _)).trans ?_
    rw [sum_sigma, mul_sum]
    apply sum_le_sum
    intro n hn
    have hn1 := (mem_Icc.mp hn).1
    have hmul : ∑ q ∈ (Icc 1 N).filter (n ∣ ·), 1 / (q.totient : ℝ) ≤
        Kc (1 / 4) * (2 * Real.log x) / n.totient := by
      refine (sum_multiples_inv_totient_le n N hn1).trans ?_
      have hlog : 1 + Real.log N ≤ 2 * Real.log x := by
        have : Real.log N ≤ Real.log x := Real.log_le_log (by exact_mod_cast hN1) hNx
        linarith
      calc 1 / (n.totient : ℝ) * ∑ m ∈ Icc 1 N, 1 / (m.totient : ℝ)
          ≤ 1 / (n.totient : ℝ) * (Kc (1 / 4) * (2 * Real.log x)) :=
            mul_le_mul_of_nonneg_left ((sum_inv_totient_le N).trans
              (mul_le_mul_of_nonneg_left hlog hK0)) (by positivity)
        _ = _ := by ring
    simp only [hP, sum_div, mul_sum]
    apply sum_le_sum
    intro χ _
    calc ∑ q ∈ (Icc 1 N).filter (n ∣ ·), G ⟨n, χ⟩ * (1 / (q.totient : ℝ))
        = G ⟨n, χ⟩ * ∑ q ∈ (Icc 1 N).filter (n ∣ ·), 1 / (q.totient : ℝ) := (mul_sum _ _ _).symm
      _ ≤ G ⟨n, χ⟩ * (Kc (1 / 4) * (2 * Real.log x) / n.totient) :=
          mul_le_mul_of_nonneg_left hmul (norm_nonneg _)
      _ = _ := by ring
  -- the totient lower bound
  have hD : ∑ n ∈ Icc 1 N, P n / n.totient ≤
      Kc (1 / 4) * (2 * Real.log x) * ∑ n ∈ Icc 1 N, P n / n := by
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    have hn1 := (mem_Icc.mp hn).1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hφ : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn1
    have hlog : 1 + Real.log n ≤ 2 * Real.log x := by
      have : Real.log n ≤ Real.log x :=
        Real.log_le_log hnpos ((Nat.cast_le.mpr (mem_Icc.mp hn).2).trans hNx)
      linarith
    have h2 : (n : ℝ) / n.totient ≤ Kc (1 / 4) * (2 * Real.log x) :=
      (self_div_totient_le hn1).trans (mul_le_mul_of_nonneg_left hlog hK0)
    have hP0n := hP0 n
    calc P n / n.totient = P n / n * ((n : ℝ) / n.totient) := by field_simp
      _ ≤ P n / n * (Kc (1 / 4) * (2 * Real.log x)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  -- the number of dyadic blocks
  have hJ : (Nat.log 2 N : ℝ) + 1 ≤ 3 * Real.log x := by
    have h2J : (2 : ℝ) ^ (Nat.log 2 N) ≤ x := by
      have h1 := Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
      have : ((2 ^ Nat.log 2 N : ℕ) : ℝ) ≤ N := by exact_mod_cast h1
      push_cast at this
      linarith
    have := Real.log_le_log (by positivity) h2J
    rw [Real.log_pow] at this
    have := Real.log_two_gt_d9
    have hJ0 : (0 : ℝ) ≤ Nat.log 2 N := Nat.cast_nonneg _
    nlinarith
  have hr : Real.log x ^ (3 : ℝ) = Real.log x ^ 3 := by
    exact_mod_cast Real.rpow_natCast (Real.log x) 3
  rw [hr]
  set L := Real.log x with hLdef
  have hL0 : 0 ≤ L := by linarith
  have hQ'0 : 0 < Q' := by linarith
  have hT : 0 ≤ primSum Q' h' z' / Q' := div_nonneg hPS hQ'0.le
  have hdy' : ∑ n ∈ Icc 1 N, P n / n ≤ 2 * (3 * L) * (primSum Q' h' z' / Q') := by
    calc ∑ n ∈ Icc 1 N, P n / n ≤ 2 * ((Nat.log 2 N : ℝ) + 1) / Q' * primSum Q' h' z' := hdy
      _ = 2 * ((Nat.log 2 N : ℝ) + 1) * (primSum Q' h' z' / Q') := by ring
      _ ≤ 2 * (3 * L) * (primSum Q' h' z' / Q') := by
          apply mul_le_mul_of_nonneg_right _ hT; linarith
  have hKL : 0 ≤ Kc (1 / 4) * (2 * L) := by positivity
  have hmain : ∑ q ∈ Icc 1 N, (1 / (q.totient : ℝ)) *
      ∑ χ : DirichletCharacter ℂ q, G ⟨χ.conductor, χ.primitiveCharacter⟩ ≤
        24 * Kc (1 / 4) ^ 2 * (L ^ 3 / Q' * primSum Q' h' z') := by
    calc _ ≤ Kc (1 / 4) * (2 * L) * ∑ n ∈ Icc 1 N, P n / n.totient := hC
      _ ≤ Kc (1 / 4) * (2 * L) * (Kc (1 / 4) * (2 * L) * (2 * (3 * L) *
            (primSum Q' h' z' / Q'))) :=
          mul_le_mul_of_nonneg_left (hD.trans (mul_le_mul_of_nonneg_left hdy' hKL)) hKL
      _ = 24 * Kc (1 / 4) ^ 2 * (L ^ 3 / Q' * primSum Q' h' z') := by ring
  have herr : (N : ℝ) * (4 * L ^ 3) ≤ 24 * Kc (1 / 4) ^ 2 * Q * L ^ 3 := by
    have hL3 : 0 ≤ L ^ 3 := by positivity
    have hK2 : 4 ≤ 24 * Kc (1 / 4) ^ 2 := by nlinarith
    have hQ0 : 0 ≤ Q := by linarith
    calc (N : ℝ) * (4 * L ^ 3) ≤ Q * (4 * L ^ 3) :=
          mul_le_mul_of_nonneg_right hNQ (by positivity)
      _ = 4 * (Q * L ^ 3) := by ring
      _ ≤ 24 * Kc (1 / 4) ^ 2 * (Q * L ^ 3) :=
          mul_le_mul_of_nonneg_right hK2 (by positivity)
      _ = _ := by ring
  calc ∑ q ∈ Icc 1 N, ppsTerm (z q) (h q) q (a q)
      ≤ ∑ q ∈ Icc 1 N, ((1 / (q.totient : ℝ)) *
          ∑ χ : DirichletCharacter ℂ q, G ⟨χ.conductor, χ.primitiveCharacter⟩ +
            4 * L ^ 3) := sum_le_sum hA
    _ = ∑ q ∈ Icc 1 N, (1 / (q.totient : ℝ)) *
          ∑ χ : DirichletCharacter ℂ q, G ⟨χ.conductor, χ.primitiveCharacter⟩ +
            (N : ℝ) * (4 * L ^ 3) := by
        rw [sum_add_distrib, sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp
    _ ≤ _ := add_le_add hmain herr

end LeanLab.Halupczok2012.Resplit398c

#print axioms LeanLab.Halupczok2012.Resplit398c.ppsTerm_le_primitive
#print axioms LeanLab.Halupczok2012.Resplit398c.primitiveCharacter_sigma_injective
#print axioms LeanLab.Halupczok2012.Resplit398c.regroup_primitive
#print axioms LeanLab.Halupczok2012.Resplit398c.self_div_totient_le
#print axioms LeanLab.Halupczok2012.Resplit398c.exists_dyadic_block
#print axioms LeanLab.Halupczok2012.Resplit398c.dyadic_pigeonhole
#print axioms LeanLab.Halupczok2012.Resplit398c.display4_reduction_proved
