/-
P0068 Zhan 1991, display (3.12), page 265, split for its proof on page 269, last paragraph:
"essentially the same as that of (3.11)", with the usual power moments of L-functions in place
of Lemmas 2 and 3. Split into the analogues of Propositions 1, 2, 3 of pages 266 to 268 for the
range T2 to 2 T2, and the combinatorial assembly of pages 268 and 269, Cases a) and b).
Burst 20261122, label eq312-split. Source: papers/P0068.pdf, journal pages 265 to 269, pdf
pages 7 to 11, page images at 150 dpi. AI-written Lean code, Claude. Checked only by the Lean
kernel. Binary Goldbach is OPEN.

Reading notes.
* The three Propositions keep the hypotheses on the `N_j` of pages 266 to 268 word for word,
  stated in terms of `H = N A⁻¹`: the interval length `T₂` enters only through the moment inputs.
  The target (3.12) is `(qN)^{1/2} L^{-B-c₀}` per interval of length `H`, times `|T₂| / H`.
  The mean value theorem over `[T₂, 2T₂]` gives `qT₂` in place of `qH`, and the usual second and
  fourth moments of `L(s, χ)` give `qT₂ L^c` in place of Lemmas 2 and 3. Rescaling by
  `H / T₂ ≤ 1 / (4π)`, which holds as `T₂ ≥ T₀`, each Proposition then needs at most the
  hypothesis it had for (3.11). For example in Proposition 3 one needs
  `(qT₂ + M₁)(qT₂ + M₂) L^c ≪ qN (T₂/H)² L^{-2B-2c₀}`, which follows from `M_i ≪ A L^{-c₆}`,
  `M₁ M₂ ≪ N`, `q ≤ A² N⁻¹ L^{-c₁}` and `A T₂ ≥ 4π N`.
* `≪` in (3.16) is read with implied constant `1`, and the boundary of Cases a) and b) is read
  as in the sibling split of (3.11): Case a) is "at most one `N_j > N^{1/5}`".
* The combinatorial lemmas below are copies, under the suffix `_312`, of the PROVED lemmas of
  `SPLIT_eq311_1122d.lean`, which is not imported since it has no built olean.
-/
import LeanLab.Zhan1991.SPLIT_theorem2_1122

namespace LeanLab.Zhan1991
open Finset Real

noncomputable section

/-- Proposition 1 for (3.12), page 269 last paragraph with page 266: there is `c₅ > 0` such
that, if some `N_{j₀} ≥ N A⁻¹ L^{c₅}`, then (3.12) holds. Same format as `Eq312`. -/
def Prop1_312 : Prop :=
  ∀ B : ℝ, 0 < B → ∀ c0 : ℝ, 0 < c0 → ∀ ε : ℝ, 0 < ε → ∃ c5 : ℝ, 0 < c5 ∧ ∃ c1m : ℝ,
    ∀ c1 ≥ c1m, ∃ c2m : ℝ, ∀ c2 ≥ c2m, ∃ c3 : ℝ, 0 < c3 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (A lam : ℝ) (q : ℕ) [NeZero q] (Nv : Fin 20 → ℝ) (T2 : ℝ), N₀ ≤ N →
      Hyp2 c1 c2 c3 N A lam q → Cond35 N Nv → T0cut N A lam ≤ |T2| →
      |T2| ≤ 2 * Tcut q N A lam ε →
      (∃ j, (N : ℝ) / A * Real.log N ^ c5 ≤ Nv j) →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
        ∫ t in Set.uIoc T2 (2 * T2), ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
        ≤ K * ((q : ℝ) / N) ^ (1 / 2 : ℝ) * A * |T2| * Real.log N ^ (-B - c0)

/-- Proposition 2 for (3.12), page 269 last paragraph with page 267: if `N_j ≤ N A⁻¹ L^{c₅}`
for all `1 ≤ j ≤ 20` and there are `j₁ ≠ j₂` with `N_{j₁} N_{j₂} ≥ (N A⁻¹)^{4/3+δ}`, then (3.12)
holds. Stated for every `δ > 0` and every `c₅ > 0`; `δ` is the `ε` of (3.18), and the `ε` of
`Eq312` is the one of (3.7). -/
def Prop2_312 : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ B : ℝ, 0 < B → ∀ c0 : ℝ, 0 < c0 → ∀ ε : ℝ, 0 < ε → ∀ c5 : ℝ, 0 < c5 →
    ∃ c1m : ℝ, ∀ c1 ≥ c1m, ∃ c2m : ℝ, ∀ c2 ≥ c2m, ∃ c3 : ℝ, 0 < c3 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (A lam : ℝ) (q : ℕ) [NeZero q] (Nv : Fin 20 → ℝ) (T2 : ℝ), N₀ ≤ N →
      Hyp2 c1 c2 c3 N A lam q → Cond35 N Nv → T0cut N A lam ≤ |T2| →
      |T2| ≤ 2 * Tcut q N A lam ε →
      (∀ j, Nv j ≤ (N : ℝ) / A * Real.log N ^ c5) →
      (∃ i j, i ≠ j ∧ ((N : ℝ) / A) ^ ((4 / 3 : ℝ) + δ) ≤ Nv i * Nv j) →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
        ∫ t in Set.uIoc T2 (2 * T2), ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
        ≤ K * ((q : ℝ) / N) ^ (1 / 2 : ℝ) * A * |T2| * Real.log N ^ (-B - c0)

/-- Proposition 3 for (3.12), page 269 last paragraph with pages 267 and 268, display (3.16):
if `J = {1, …, 20}` splits into `J₁` and `J₂ = J \ J₁` with
`max (Π_{J₁} N_j, Π_{J₂} N_j) ≪ A L^{-c₆}`, `c₆` sufficiently large, then (3.12) holds. -/
def Prop3_312 : Prop :=
  ∀ B : ℝ, 0 < B → ∀ c0 : ℝ, 0 < c0 → ∀ ε : ℝ, 0 < ε → ∃ c6m : ℝ, ∀ c6 ≥ c6m, ∃ c1m : ℝ,
    ∀ c1 ≥ c1m, ∃ c2m : ℝ, ∀ c2 ≥ c2m, ∃ c3 : ℝ, 0 < c3 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (A lam : ℝ) (q : ℕ) [NeZero q] (Nv : Fin 20 → ℝ) (T2 : ℝ), N₀ ≤ N →
      Hyp2 c1 c2 c3 N A lam q → Cond35 N Nv → T0cut N A lam ≤ |T2| →
      |T2| ≤ 2 * Tcut q N A lam ε →
      ∀ J1 : Finset (Fin 20), ∏ j ∈ J1, Nv j ≤ A * Real.log N ^ (-c6) →
      ∏ j ∈ J1ᶜ, Nv j ≤ A * Real.log N ^ (-c6) →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
        ∫ t in Set.uIoc T2 (2 * T2), ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
        ≤ K * ((q : ℝ) / N) ^ (1 / 2 : ℝ) * A * |T2| * Real.log N ^ (-B - c0)

/-- LEAF: Proposition 1 for (3.12), page 269 last paragraph, as page 266 to page 267 top:
Perron's formula for `f_{j₀}` with `c = 1/2 + L⁻¹`, the line shift, the usual second power
moment `Σ_χ ∫_{T₂}^{2T₂} |L'(1/2+it, χ)|² dt ≪ qT₂ L^c` in place of Lemma 2, then Cauchy, the
mean value theorem for Dirichlet polynomials, Lemma 6, and (3.13). Class HARD. -/
theorem prop1_312_leaf : Prop1_312 := by
  sorry

/-- LEAF: Proposition 2 for (3.12), page 269 last paragraph, as page 267, displays (3.14) and
(3.15): Perron for `f₁, f₂`, the usual fourth power moment
`Σ_χ ∫_{T₂}^{2T₂} |L'(1/2+it, χ)|⁴ dt ≪ qT₂ L^c` in place of Lemma 3, Hölder, Lemma 6 and
(3.13). Class HARD. -/
theorem prop2_312_leaf : Prop2_312 := by
  sorry

/-- LEAF: Proposition 3 for (3.12), page 269 last paragraph, as pages 267 and 268, display
(3.16): Cauchy with `F = F₁ F₂`, the mean value theorem over `[T₂, 2T₂]`, Lemma 6 and (3.13).
Class HARD. -/
theorem prop3_312_leaf : Prop3_312 := by
  sorry

/-! ### The combinatorial assembly of pages 268 and 269, PROVED -/

/-- PROVED: the hypotheses of Theorem 2 are monotone in `c₃`, since `L ≥ 1`. -/
theorem hyp2_mono_c3_312 {c1 c2 c3 c3' : ℝ} {N : ℕ} {A lam : ℝ} {q : ℕ} (h : c3 ≤ c3')
    (hL : 1 ≤ Real.log N) (hH : Hyp2 c1 c2 c3' N A lam q) : Hyp2 c1 c2 c3 N A lam q := by
  obtain ⟨h1, h2⟩ := hH
  exact ⟨le_trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL h)
    (by positivity)) h1, h2⟩

/-- PROVED, page 268, Case a): the greedy choice of `j₁, …, j_{l+1}`. Starting from a product
`P ≤ X` and adding factors `≤ Y` one at a time, either the product first exceeds `X`, when it is
still `≤ X Y`, or all factors are used. -/
theorem greedy_312 (Nv : Fin 20 → ℝ) (X Y P : ℝ) (hY : 1 ≤ Y) (hP : 0 < P)
    (hPX : P ≤ X) (S : Finset (Fin 20)) (hS : ∀ j ∈ S, 0 < Nv j ∧ Nv j ≤ Y) :
    ∃ T ⊆ S, P * ∏ j ∈ T, Nv j ≤ X * Y ∧ (X < P * ∏ j ∈ T, Nv j ∨ T = S) := by
  revert hS
  refine Finset.induction_on S ?_ ?_
  · intro _
    refine ⟨∅, Finset.Subset.refl _, ?_, Or.inr rfl⟩
    simp only [Finset.prod_empty, mul_one]
    nlinarith
  · intro a S' ha ih hS
    obtain ⟨T', hT', hb, hor⟩ := ih (fun j hj => hS j (Finset.mem_insert_of_mem hj))
    rcases hor with h | h
    · exact ⟨T', hT'.trans (Finset.subset_insert _ _), hb, Or.inl h⟩
    · subst h
      by_cases hx : X < P * ∏ j ∈ T', Nv j
      · exact ⟨T', Finset.subset_insert _ _, hb, Or.inl hx⟩
      · push_neg at hx
        refine ⟨insert a T', Finset.Subset.refl _, ?_, Or.inr rfl⟩
        obtain ⟨ha0, haY⟩ := hS a (Finset.mem_insert_self _ _)
        rw [Finset.prod_insert ha]
        calc P * (Nv a * ∏ j ∈ T', Nv j) = (P * ∏ j ∈ T', Nv j) * Nv a := by ring
          _ ≤ X * Y := mul_le_mul hx haY ha0.le (by linarith)

/-- PROVED, pages 268 and 269, Cases a) and b): under (3.5), `A ≥ N^{3/5} L^{c₃}`, (3.17) and
(3.18) with `ε = 1/6`, and `c₅ ≤ c₆ ≤ c₃`, the index set splits as in (3.16). -/
theorem partition_312 {N : ℕ} {A c3 c5 c6 : ℝ} {Nv : Fin 20 → ℝ}
    (hL : 1 ≤ Real.log N) (hc6 : 0 ≤ c6) (hc56 : c5 ≤ c6) (hc36 : c6 ≤ c3)
    (hA1 : (N : ℝ) ^ (3 / 5 : ℝ) * Real.log N ^ c3 ≤ A) (hC : Cond35 N Nv)
    (h317 : ∀ j, Nv j ≤ (N : ℝ) / A * Real.log N ^ c5)
    (h318 : ∀ i j, i ≠ j → Nv i * Nv j ≤ ((N : ℝ) / A) ^ ((4 / 3 : ℝ) + 1 / 6)) :
    ∃ J1 : Finset (Fin 20), ∏ j ∈ J1, Nv j ≤ A * Real.log N ^ (-c6) ∧
      ∏ j ∈ J1ᶜ, Nv j ≤ A * Real.log N ^ (-c6) := by
  have hN0 : (N : ℝ) ≠ 0 := by
    intro h; rw [h, Real.log_zero] at hL; linarith
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (by exact_mod_cast hN0))
  have hNp : (0 : ℝ) ≤ N := by linarith
  set L := Real.log N with hLdef
  set s : ℝ := (N : ℝ) ^ (1 / 5 : ℝ) with hsdef
  have hs1 : 1 ≤ s := Real.one_le_rpow hN1 (by norm_num)
  have hs0 : 0 < s := by linarith
  have hs5 : s ^ 5 = N := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hNp]; norm_num
  have hs3 : (N : ℝ) ^ (3 / 5 : ℝ) = s ^ 3 := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hNp]; norm_num
  set l : ℝ := L ^ c6 with hldef
  have hl1 : 1 ≤ l := Real.one_le_rpow hL hc6
  have hl0 : 0 < l := by linarith
  have hl5 : L ^ c5 ≤ l := Real.rpow_le_rpow_of_exponent_le hL hc56
  have hl3 : l ≤ L ^ c3 := Real.rpow_le_rpow_of_exponent_le hL hc36
  have hM : L ^ (-c6) = l⁻¹ := Real.rpow_neg (by linarith) c6
  rw [hM]
  have hA : s ^ 3 * l ≤ A := by
    rw [hs3] at hA1
    exact le_trans (mul_le_mul_of_nonneg_left hl3 (by positivity)) hA1
  have hApos : 0 < A := lt_of_lt_of_le (by positivity) hA
  have hNv : ∀ j, 0 < Nv j := fun j => lt_of_lt_of_le (by norm_num) (hC.1 j)
  have hprod : ∏ j, Nv j ≤ s ^ 5 := hs5 ▸ hC.2.2.1
  have hsplit : ∀ J : Finset (Fin 20), (∏ j ∈ J, Nv j) * ∏ j ∈ Jᶜ, Nv j ≤ s ^ 5 := by
    intro J; rw [Finset.prod_mul_prod_compl]; exact hprod
  have hpos : ∀ J : Finset (Fin 20), 0 < ∏ j ∈ J, Nv j :=
    fun J => Finset.prod_pos (fun j _ => hNv j)
  -- the four size facts
  have F3 : s ^ 3 ≤ A * l⁻¹ := by
    rw [le_mul_inv_iff₀ hl0]; exact hA
  have F1 : (N : ℝ) / A * l * s ≤ A * l⁻¹ := by
    rw [← hs5, le_mul_inv_iff₀ hl0, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_le_iff₀ hApos]
    have h2 : (s ^ 3 * l) ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (by positivity) hA 2
    nlinarith
  have F4 : ((N : ℝ) / A) ^ ((4 / 3 : ℝ) + 1 / 6) ≤ A * l⁻¹ := by
    have hr : (0 : ℝ) ≤ (N : ℝ) / A := by positivity
    have he : ((N : ℝ) / A) ^ ((4 / 3 : ℝ) + 1 / 6) = (((N : ℝ) / A) ^ (1 / 2 : ℝ)) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr]; norm_num
    rw [he]
    set u := ((N : ℝ) / A) ^ (1 / 2 : ℝ) with hu
    have hu0 : 0 ≤ u := by positivity
    have hu2 : u ^ 2 = (N : ℝ) / A := by
      rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hr]; norm_num
    have hAl : 0 ≤ A * l⁻¹ := by positivity
    rw [← pow_le_pow_iff_left₀ (by positivity) hAl (by norm_num : (2 : ℕ) ≠ 0)]
    have h6 : (u ^ 3) ^ 2 = (s ^ 5 / A) ^ 3 := by
      calc (u ^ 3) ^ 2 = (u ^ 2) ^ 3 := by ring
        _ = (s ^ 5 / A) ^ 3 := by rw [hu2, hs5]
    have h5 : (s ^ 3 * l) ^ 5 ≤ A ^ 5 := pow_le_pow_left₀ (by positivity) hA 5
    have hl25 : l ^ 2 ≤ l ^ 5 := pow_le_pow_right₀ hl1 (by norm_num)
    have key : (s ^ 5) ^ 3 * l ^ 2 ≤ A ^ 5 := by
      have : (s ^ 5) ^ 3 * l ^ 2 ≤ (s ^ 5) ^ 3 * l ^ 5 :=
        mul_le_mul_of_nonneg_left hl25 (by positivity)
      calc (s ^ 5) ^ 3 * l ^ 2 ≤ (s ^ 5) ^ 3 * l ^ 5 := this
        _ = (s ^ 3 * l) ^ 5 := by ring
        _ ≤ A ^ 5 := h5
    rw [h6, div_pow, mul_pow, inv_pow, div_le_iff₀ (by positivity)]
    have hl2 : (0 : ℝ) < l ^ 2 := by positivity
    calc (s ^ 5) ^ 3 = (s ^ 5) ^ 3 * l ^ 2 * (l ^ 2)⁻¹ := by field_simp
      _ ≤ A ^ 5 * (l ^ 2)⁻¹ := mul_le_mul_of_nonneg_right key (by positivity)
      _ = A ^ 2 * (l ^ 2)⁻¹ * A ^ 3 := by ring
  have hM1 : 1 ≤ A * l⁻¹ := le_trans (one_le_pow₀ hs1) F3
  by_cases hb : ∃ i j, i ≠ j ∧ s < Nv i ∧ s < Nv j
  · -- Case b), page 269
    obtain ⟨i, j, hij, hi, hj⟩ := hb
    refine ⟨{i, j}, ?_, ?_⟩
    · rw [Finset.prod_pair hij]; exact le_trans (h318 i j hij) F4
    · have h1 := hsplit {i, j}
      rw [Finset.prod_pair hij] at h1
      have hP2 := hpos ({i, j}ᶜ)
      have hss : s * s < Nv i * Nv j := mul_lt_mul'' hi hj hs0.le hs0.le
      have : (∏ k ∈ ({i, j} : Finset (Fin 20))ᶜ, Nv k) * (s * s) < s ^ 3 * (s * s) := by
        calc (∏ k ∈ ({i, j} : Finset (Fin 20))ᶜ, Nv k) * (s * s)
            < (∏ k ∈ ({i, j} : Finset (Fin 20))ᶜ, Nv k) * (Nv i * Nv j) :=
              mul_lt_mul_of_pos_left hss hP2
          _ = Nv i * Nv j * ∏ k ∈ ({i, j} : Finset (Fin 20))ᶜ, Nv k := by ring
          _ ≤ s ^ 5 := h1
          _ = s ^ 3 * (s * s) := by ring
      exact le_trans (lt_of_mul_lt_mul_right this (by positivity)).le F3
  · -- Case a), page 268
    push_neg at hb
    have hj0 : ∃ j0, ∀ j, j ≠ j0 → Nv j ≤ s := by
      by_cases h : ∃ j0, s < Nv j0
      · obtain ⟨j0, hj0⟩ := h
        exact ⟨j0, fun j hj => hb j0 j (Ne.symm hj) hj0⟩
      · push_neg at h
        exact ⟨0, fun j _ => h j⟩
    obtain ⟨j0, hj0⟩ := hj0
    set X : ℝ := (N : ℝ) / A * l with hX
    have hX0 : Nv j0 ≤ X := le_trans (h317 j0) (mul_le_mul_of_nonneg_left hl5 (by positivity))
    obtain ⟨T, hT, hb1, hor⟩ := greedy_312 Nv X s (Nv j0) hs1 (hNv j0) hX0
      (Finset.univ.erase j0) (fun j hj => ⟨hNv j, hj0 j (Finset.ne_of_mem_erase hj)⟩)
    have hj0T : j0 ∉ T := fun h => (Finset.notMem_erase j0 _) (hT h)
    refine ⟨insert j0 T, ?_, ?_⟩
    · rw [Finset.prod_insert hj0T]; exact le_trans hb1 F1
    · rcases hor with h | h
      · have h1 := hsplit (insert j0 T)
        rw [Finset.prod_insert hj0T] at h1
        have hP2 := hpos ((insert j0 T)ᶜ)
        have hXpos : 0 < X := by positivity
        have hMX : A * l⁻¹ * X = s ^ 5 := by
          rw [hX, ← hs5]; field_simp
        have : (∏ k ∈ (insert j0 T)ᶜ, Nv k) * X < A * l⁻¹ * X := by
          calc (∏ k ∈ (insert j0 T)ᶜ, Nv k) * X
              < (∏ k ∈ (insert j0 T)ᶜ, Nv k) * (Nv j0 * ∏ k ∈ T, Nv k) :=
                mul_lt_mul_of_pos_left h hP2
            _ = Nv j0 * (∏ k ∈ T, Nv k) * ∏ k ∈ (insert j0 T)ᶜ, Nv k := by ring
            _ ≤ s ^ 5 := h1
            _ = A * l⁻¹ * X := hMX.symm
        exact (lt_of_mul_lt_mul_right this hXpos.le).le
      · rw [h, Finset.insert_erase (Finset.mem_univ _), Finset.compl_univ, Finset.prod_empty]
        exact hM1

/-- PROVED, pages 268 and 269 with page 269 last paragraph: (3.12) from Propositions 1, 2 and 3
for (3.12), with `δ = 1/6` in Proposition 2, `c₆ = max (c₆ of Prop 3, c₅ + 1)` and `c₃` the
maximum of the three `c₃` and `c₆`, exactly as for (3.11). -/
theorem eq312_of_props (h1 : Prop1_312) (h2 : Prop2_312) (h3 : Prop3_312) :
    Eq312 := by
  intro B hB c0 hc0 ε hε
  obtain ⟨c5, hc5, P1⟩ := h1 B hB c0 hc0 ε hε
  obtain ⟨c6m, P3⟩ := h3 B hB c0 hc0 ε hε
  set c6 := max c6m (c5 + 1) with hc6
  obtain ⟨c1m3, P3⟩ := P3 c6 (le_max_left _ _)
  obtain ⟨c1m2, P2⟩ := h2 (1 / 6) (by norm_num) B hB c0 hc0 ε hε c5 hc5
  obtain ⟨c1m1, P1⟩ := P1
  refine ⟨max c1m1 (max c1m2 c1m3), fun c1 hc1 => ?_⟩
  obtain ⟨c2m1, P1⟩ := P1 c1 (le_trans (le_max_left _ _) hc1)
  obtain ⟨c2m2, P2⟩ := P2 c1 (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hc1)
  obtain ⟨c2m3, P3⟩ := P3 c1 (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hc1)
  refine ⟨max c2m1 (max c2m2 c2m3), fun c2 hc2 => ?_⟩
  obtain ⟨c3a, hc3a, K1, N1, P1⟩ := P1 c2 (le_trans (le_max_left _ _) hc2)
  obtain ⟨c3b, hc3b, K2, N2, P2⟩ :=
    P2 c2 (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hc2)
  obtain ⟨c3c, hc3c, K3, N3, P3⟩ :=
    P3 c2 (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hc2)
  have hc6p : 0 ≤ c6 := le_trans (by linarith) (le_max_right c6m (c5 + 1))
  set c3 := max (max c3a c3b) (max c3c c6) with hc3
  refine ⟨c3, lt_of_lt_of_le hc3a (le_trans (le_max_left _ _) (le_max_left _ _)),
    max K1 (max K2 K3), max (max N1 N2) (max N3 3), ?_⟩
  intro N A lam q _ Nv T2 hN hH hC hT hT'
  have hN3 : (3 : ℝ) ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hN3
  have hA0 : 0 ≤ A := le_trans (by positivity) hH.1
  have hR : 0 ≤ ((q : ℝ) / N) ^ (1 / 2 : ℝ) * A * |T2| * Real.log N ^ (-B - c0) := by
    positivity
  have mono : ∀ Ki : ℝ, Ki ≤ max K1 (max K2 K3) →
      Ki * ((q : ℝ) / N) ^ (1 / 2 : ℝ) * A * |T2| * Real.log N ^ (-B - c0)
        ≤ max K1 (max K2 K3) * ((q : ℝ) / N) ^ (1 / 2 : ℝ) * A * |T2| *
          Real.log N ^ (-B - c0) := by
    intro Ki hK
    have e : ∀ K' : ℝ, K' * ((q : ℝ) / N) ^ (1 / 2 : ℝ) * A * |T2| * Real.log N ^ (-B - c0)
        = K' * (((q : ℝ) / N) ^ (1 / 2 : ℝ) * A * |T2| * Real.log N ^ (-B - c0)) :=
      fun _ => by ring
    rw [e, e]
    exact mul_le_mul_of_nonneg_right hK hR
  have hNa : N1 ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb : N2 ≤ (N : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNc : N3 ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hHa := hyp2_mono_c3_312 (le_trans (le_max_left _ _) (le_max_left _ _)) hL hH
  have hHb := hyp2_mono_c3_312 (le_trans (le_max_right _ _) (le_max_left _ _)) hL hH
  have hHc := hyp2_mono_c3_312 (le_trans (le_max_left _ _) (le_max_right _ _)) hL hH
  by_cases e1 : ∃ j, (N : ℝ) / A * Real.log N ^ c5 ≤ Nv j
  · exact le_trans (P1 N A lam q Nv T2 hNa hHa hC hT hT' e1) (mono K1 (le_max_left _ _))
  push_neg at e1
  have h317 : ∀ j, Nv j ≤ (N : ℝ) / A * Real.log N ^ c5 := fun j => (e1 j).le
  by_cases e2 : ∃ i j, i ≠ j ∧ ((N : ℝ) / A) ^ ((4 / 3 : ℝ) + 1 / 6) ≤ Nv i * Nv j
  · exact le_trans (P2 N A lam q Nv T2 hNb hHb hC hT hT' h317 e2)
      (mono K2 (le_trans (le_max_left _ _) (le_max_right _ _)))
  push_neg at e2
  obtain ⟨J1, hJ1, hJ2⟩ := partition_312 hL hc6p
    (le_trans (by linarith) (le_max_right c6m (c5 + 1)))
    (le_trans (le_max_right _ _) (le_max_right _ _)) hH.1 hC h317
    (fun i j hij => (e2 i j hij).le)
  exact le_trans (P3 N A lam q Nv T2 hNc hHc hC hT hT' J1 hJ1 hJ2)
    (mono K3 (le_trans (le_max_right _ _) (le_max_right _ _)))

/-- (3.12) from the three LEAF Propositions for (3.12), pages 265 to 269. -/
theorem eq312_split : Eq312 :=
  eq312_of_props prop1_312_leaf prop2_312_leaf prop3_312_leaf

end

end LeanLab.Zhan1991
