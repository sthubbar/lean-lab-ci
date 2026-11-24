import LeanLab.ExceptionalSet.UpJ200.Lemma3MVSplit

/-!
# Repair of the leaf `mv_71_tilde`: the faithful small `θ` twin and its split

Burst burst-20261122, unit lemma3_split-mv71repair.

A reviewer judged the LEAF `Lemma3MVSplit.mv_71_tilde` stronger than its source: it asserts
P0015 display (7.1̃), page 366, for every `θ < 6/100` with `B`, `c₆` uniform, while MV derive
(7.1̃) from Lemma 4.3, page 357, which needs `exp(log^{1/2} N) ≤ P ≤ N^{c₄}` with `c₄` a small
absolute constant. That leaf is not edited here.

Structure.
* DEFINITION `sharpSumTilde`: P0015 page 357, the `Σ^#` of Lemma 4.3 for the exceptional character,
  `Σ χ̃(p) log p + Σ n^{β̃-1}`.
* PROVED `gall42_generic`, `wnormTilde_le`: the Lemma 4.2 step of page 366 for the exceptional
  `W(χ̃)` of page 361, by the lab's proved discrete Gallagher inequality `gall42_gallagher`. For the
  other characters the existing proved `Lemma2MVSplit.mv_gallagher_lemma42_step` is reused.
* LEAF `mv_gallagher_lemma43_tilde`: P0015 Lemma 4.3 in the exceptional case, the right side
  reduced by the factor `(1-β̃) log P`, Gallagher 1970 Theorem 7, class HARD, CITED.
* PROVED from that one leaf: `mv_71_tilde_small`, the faithful twin of `mv_71_tilde` with
  `θ < θ₁`, and `bpLemma3HypSmall_of_leaves`, P0082 Lemma 3 for `θ < θ₁`, from
  `Lemma3MVSplit.mv_617_tilde` and `Lemma3MVSplit.w_terms_le`.
* PROVED sorry free sanity twins: `mv_71_tilde` implies `mv_71_tilde_small`, and `BPLemma3Hyp`
  implies the small form, so the new statements are weaker than the old ones.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Lemma3MV71Repair

open Real Finset Filter
open LeanLab.ExceptionalSet.U1539 (R1 eC)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)
open LeanLab.ExceptionalSet.UpJ200.Decomp559b (SelectedRealZero)
open LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected (singSeries)
open LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082 (twistedSing Itilde)
open LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082 (BPLemma3Hyp)
open LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit
  (Wchi Schi Wnorm mvW sharpSum mv_gallagher_lemma42_step gall42_Wchi_eq gall42_sharp_eq)
open LeanLab.ExceptionalSet.UpJ200.Lemma2MV (gall42_S gall42_B gall42_gallagher)
open LeanLab.ExceptionalSet.UpJ200.Lemma3MVSplit
  (Ttilde WnormTilde mvWtilde mv_617_tilde mv_71_tilde w_terms_le)

/-! ### Definition -/

/-- P0015 page 357, Lemma 4.3: "if there is an exceptional character `χ̃` then the corresponding
term is `Σ_{x-h}^{x} χ̃(p) log p + Σ_{x-h<n≤x, n>0} n^{β̃-1}`", restricted to `P < n ≤ X` as in the
first display of section 7, page 366. These are the coefficients of `W(χ̃,η) = S(χ̃,η) - T̃(η)`. -/
noncomputable def sharpSumTilde {r : ℕ} (β P X : ℝ) (χ : DirichletCharacter ℂ r) (x h : ℝ) : ℂ :=
  ∑ n ∈ (Ioc ⌊P⌋₊ ⌊X⌋₊).filter (fun n : ℕ => x - h < (n : ℝ) ∧ (n : ℝ) ≤ x),
    ((if Nat.Prime n then (Real.log n : ℂ) * χ (n : ZMod r) else 0) +
      (((n : ℝ) ^ (β - 1) : ℝ) : ℂ))

/-! ### Bridges, PROVED -/

/-- P0015 page 361: for `χ̃ ≠ χ₀`, `W(χ̃,η) = S(χ̃,η) - T̃(η)` is the exponential sum with the
coefficients of the exceptional `Σ^#` of page 357. -/
lemma wtilde_eq {r : ℕ} (β P X : ℝ) (χ : DirichletCharacter ℂ r) (hχ : χ ≠ 1) (η : ℝ) :
    Wchi P X χ η - Ttilde β P X η = gall42_S (Ioc ⌊P⌋₊ ⌊X⌋₊) (fun n =>
      (if Nat.Prime n then (Real.log n : ℂ) * χ (n : ZMod r) else 0) +
        (((n : ℝ) ^ (β - 1) : ℝ) : ℂ)) η := by
  classical
  unfold Wchi Schi Ttilde gall42_S
  rw [if_neg hχ, sub_zero, sub_neg_eq_add, sum_filter, ← sum_add_distrib]
  refine sum_congr rfl (fun n _ => ?_)
  by_cases hp : Nat.Prime n <;> simp only [hp, if_true, if_false] <;> ring

/-- P0015 page 366: the exceptional `Σ^#_{m-H<n≤m}` at integer `m`, `H` is the block sum of
Lemma 4.2. -/
lemma sharpTilde_eq {r : ℕ} (β P X : ℝ) (χ : DirichletCharacter ℂ r) (m H : ℕ) :
    sharpSumTilde β P X χ (m : ℝ) (H : ℝ) = gall42_B (Ioc ⌊P⌋₊ ⌊X⌋₊) (fun n =>
      (if Nat.Prime n then (Real.log n : ℂ) * χ (n : ZMod r) else 0) +
        (((n : ℝ) ^ (β - 1) : ℝ) : ℂ)) H m := by
  unfold sharpSumTilde gall42_B
  refine sum_congr (filter_congr (fun n _ => ?_)) (fun _ _ => rfl)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by exact_mod_cast h2, ?_⟩
    have : (m : ℝ) < n + H := by linarith
    exact_mod_cast this
  · rintro ⟨h1, h2⟩
    have h1' : (n : ℝ) ≤ m := by exact_mod_cast h1
    have h2' : (m : ℝ) < n + H := by exact_mod_cast h2
    exact ⟨by linarith, h1'⟩

/-! ### The Lemma 4.2 step of page 366 for any coefficients, PROVED -/

/-- P0015 page 366, first display of section 7, from Lemma 4.2, for arbitrary coefficients `a`
on `P < n ≤ X`: if every block sum `Σ_{m-H<n≤m} a n` with `m ≤ 2X`, `1 ≤ H ≤ X` is at most
`M (H + X/P)`, then `(∫_{-1/rQ}^{1/rQ} |Σ a n e(nη)|²)^{1/2} ≤ 49 X^{1/2} M`. The proof is the one
of `Lemma2MVSplit.mv_gallagher_lemma42_step`, with the coefficients left free. PROVED. -/
theorem gall42_generic (P X : ℝ) (r : ℕ) (a : ℕ → ℂ) (hX : 256 ≤ X) (hP1 : 1 ≤ P)
    (hPs : P ≤ Real.sqrt X) (hr1 : 1 ≤ r) (hrP : (r : ℝ) ≤ P) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ m H : ℕ, (m : ℝ) ≤ 2 * X → (0 : ℝ) < H → (H : ℝ) ≤ X →
      ‖gall42_B (Ioc ⌊P⌋₊ ⌊X⌋₊) a H m‖ ≤ M * (H + X / P)) :
    Real.sqrt (∫ η in (-(P / (r * X)))..(P / (r * X)), ‖gall42_S (Ioc ⌊P⌋₊ ⌊X⌋₊) a η‖ ^ 2) ≤
      49 * Real.sqrt X * M := by
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hP0 : 0 < P := by linarith
  have hsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have h16 : 16 ≤ Real.sqrt X := Real.le_sqrt_of_sq_le (by linarith)
  have hXP : 16 ≤ X / P := by
    rw [le_div_iff₀ hP0]; nlinarith
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  set Q := (r : ℝ) * X / P with hQ
  have hXPQ : X / P ≤ Q := by
    rw [hQ, mul_div_assoc]; nlinarith
  have hQX : Q ≤ X := by
    rw [hQ, div_le_iff₀ hP0]; nlinarith
  have hQ0 : 0 < Q := by linarith
  set H := ⌊Q / 8⌋₊ with hHdef
  have hHle : (H : ℝ) ≤ Q / 8 := Nat.floor_le (by positivity)
  have hHge : Q / 8 - 1 < H := Nat.sub_one_lt_floor _
  have hHpos : (0 : ℝ) < H := by linarith
  have hH1 : 1 ≤ H := by
    have : (1 : ℝ) ≤ H := by linarith
    exact_mod_cast this
  have hκ : P / (r * X) = 1 / Q := by
    rw [hQ]; field_simp
  set s := Ioc ⌊P⌋₊ ⌊X⌋₊ with hsdef
  have hs : ∀ n ∈ s, n < ⌊X⌋₊ + 1 := by
    intro n hn; have := (mem_Ioc.mp hn).2; omega
  have hcore := gall42_gallagher s a (⌊X⌋₊ + 1) H hs hH1 (1 / Q) (by positivity)
    (by rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hQ0]; linarith)
  have hHQ : X / P ≤ 16 * H := by linarith
  have hB : ∀ m ∈ range (⌊X⌋₊ + 1 + H), ‖gall42_B s a H m‖ ^ 2 ≤ (17 * M * H) ^ 2 := by
    intro m hm
    have hmlt : m < ⌊X⌋₊ + 1 + H := mem_range.mp hm
    have hmle : (m : ℝ) ≤ X + H := by
      have h1 : m ≤ ⌊X⌋₊ + H := by omega
      have h2 : ((m : ℕ) : ℝ) ≤ ((⌊X⌋₊ + H : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h2; linarith [Nat.floor_le hX0.le]
    have hb := hM m H (by linarith) hHpos (by linarith)
    have h17 : ‖gall42_B s a H m‖ ≤ 17 * M * H := le_trans hb (by nlinarith)
    exact pow_le_pow_left₀ (norm_nonneg _) h17 2
  have hsum : ∑ m ∈ range (⌊X⌋₊ + 1 + H), ‖gall42_B s a H m‖ ^ 2 ≤
      ((⌊X⌋₊ + 1 + H : ℕ) : ℝ) * (17 * M * H) ^ 2 := by
    calc _ ≤ ∑ m ∈ range (⌊X⌋₊ + 1 + H), (17 * M * H) ^ 2 := sum_le_sum hB
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]
  have hcard : ((⌊X⌋₊ + 1 + H : ℕ) : ℝ) ≤ 2 * X := by
    push_cast; linarith [Nat.floor_le hX0.le]
  have hint : ∫ η in (-(P / (r * X)))..(P / (r * X)), ‖gall42_S s a η‖ ^ 2 ≤
      2312 * X * M ^ 2 := by
    rw [hκ]
    calc _ ≤ 4 / (H : ℝ) ^ 2 * ∑ m ∈ range (⌊X⌋₊ + 1 + H), ‖gall42_B s a H m‖ ^ 2 := hcore
      _ ≤ 4 / (H : ℝ) ^ 2 * (((⌊X⌋₊ + 1 + H : ℕ) : ℝ) * (17 * M * H) ^ 2) := by gcongr
      _ ≤ 4 / (H : ℝ) ^ 2 * (2 * X * (17 * M * H) ^ 2) := by gcongr
      _ = 2312 * X * M ^ 2 := by field_simp; ring
  have h49 : 2312 * X * M ^ 2 ≤ (49 * Real.sqrt X * M) ^ 2 := by
    have : (49 * Real.sqrt X * M) ^ 2 = 2401 * (Real.sqrt X * Real.sqrt X) * M ^ 2 := by ring
    rw [this, hsq]; nlinarith [sq_nonneg M]
  exact (Real.sqrt_le_sqrt hint).trans
    ((Real.sqrt_le_sqrt h49).trans_eq (Real.sqrt_sq (by positivity)))

/-- A bound `‖z‖ ≤ M (1 + X/P)` with `X, P > 0` forces `M ≥ 0`. PROVED. -/
lemma bound_nonneg (z : ℂ) (M X P : ℝ) (hX : 0 < X) (hP : 0 < P)
    (h : ‖z‖ ≤ M * (1 + X / P)) : 0 ≤ M := by
  by_contra hn
  push_neg at hn
  have h1 : 0 < 1 + X / P := by positivity
  have := mul_neg_of_neg_of_pos hn h1
  linarith [norm_nonneg z]

/-- P0015 page 366, the Lemma 4.2 step for the exceptional `W(χ̃)` of page 361:
`W(χ̃) ≤ 49 X^{1/2} M` whenever the exceptional `Σ^#` is at most `M (h + X/P)` for `x ≤ 2X`,
`0 < h ≤ X`. Here `P = X^θ` with `θ ≤ 1/2` and `X ≥ 256`. PROVED. -/
theorem wnormTilde_le {r : ℕ} (β θ X : ℝ) (hθ : 0 < θ) (hθ2 : θ ≤ 1 / 2) (hX : 256 ≤ X)
    (hr1 : 1 ≤ r) (hrP : (r : ℝ) ≤ X ^ θ) (χ : DirichletCharacter ℂ r) (hχ : χ ≠ 1) (M : ℝ)
    (hM : ∀ x h : ℝ, 0 ≤ x → x ≤ 2 * X → 0 < h → h ≤ X →
      ‖sharpSumTilde β (X ^ θ) X χ x h‖ ≤ M * (h + X / X ^ θ)) :
    WnormTilde β (X ^ θ) X χ ≤ 49 * Real.sqrt X * M := by
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hP1 : 1 ≤ X ^ θ := Real.one_le_rpow hX1 hθ.le
  have hPs : X ^ θ ≤ Real.sqrt X := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hX1 hθ2
  have hM0 : 0 ≤ M := bound_nonneg _ M X (X ^ θ) hX0 (by linarith)
    (by simpa using hM 0 1 le_rfl (by linarith) one_pos hX1)
  have key := wtilde_eq β (X ^ θ) X χ hχ
  unfold WnormTilde
  simp_rw [key]
  refine gall42_generic (X ^ θ) X r _ hX hP1 hPs hr1 hrP M hM0 ?_
  intro m H hm hH hHX
  rw [← sharpTilde_eq]
  exact hM m H (Nat.cast_nonneg _) hm hH hHX

/-! ### Finite sum surgery, PROVED -/

/-- Removing one term from a finite `finsum`: if `F ≤ G` away from `i₀` then
`Σ F - F i₀ ≤ Σ G - G i₀`. PROVED. -/
lemma finsum_sub_le {ι : Type*} [Finite ι] (F G : ι → ℝ) (i₀ : ι)
    (h : ∀ i, i ≠ i₀ → F i ≤ G i) :
    (∑ᶠ i, F i) - F i₀ ≤ (∑ᶠ i, G i) - G i₀ := by
  classical
  haveI := Fintype.ofFinite ι
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    ← add_sum_erase univ F (mem_univ i₀), ← add_sum_erase univ G (mem_univ i₀)]
  have := sum_le_sum (fun i hi => h i (ne_of_mem_erase hi))
    (s := univ.erase i₀) (f := F) (g := G)
  linarith

/-- The sum `Σ_{q≤P} Σ*_χ` of P0015 page 366 with the one exceptional summand removed: if
`F ≤ G` at every primitive `ψ` other than `χ₀` of modulus `r`, then
`Σ Σ* F - F χ₀ ≤ Σ Σ* G - G χ₀`. PROVED. -/
lemma sum_sub_le (N r : ℕ) (hr : r ∈ Icc 1 N) (F G : (q : ℕ) → DirichletCharacter ℂ q → ℝ)
    (χ₀ : DirichletCharacter ℂ r) (hχ₀ : χ₀.IsPrimitive)
    (h1 : ∀ q ∈ Icc 1 N, q ≠ r → ∀ ψ : DirichletCharacter ℂ q, ψ.IsPrimitive → F q ψ ≤ G q ψ)
    (h2 : ∀ ψ : DirichletCharacter ℂ r, ψ.IsPrimitive → ψ ≠ χ₀ → F r ψ ≤ G r ψ) :
    (∑ q ∈ Icc 1 N, ∑ᶠ ψ : {ψ : DirichletCharacter ℂ q // ψ.IsPrimitive}, F q ψ.1) - F r χ₀ ≤
      (∑ q ∈ Icc 1 N, ∑ᶠ ψ : {ψ : DirichletCharacter ℂ q // ψ.IsPrimitive}, G q ψ.1) -
        G r χ₀ := by
  rw [← add_sum_erase _ _ hr, ← add_sum_erase _ _ hr]
  have hA : ∑ q ∈ (Icc 1 N).erase r, ∑ᶠ ψ : {ψ : DirichletCharacter ℂ q // ψ.IsPrimitive},
      F q ψ.1 ≤ ∑ q ∈ (Icc 1 N).erase r,
        ∑ᶠ ψ : {ψ : DirichletCharacter ℂ q // ψ.IsPrimitive}, G q ψ.1 := by
    refine sum_le_sum (fun q hq => ?_)
    refine finsum_le_finsum (Set.toFinite _) (Set.toFinite _) (fun ψ => ?_)
    exact h1 q (mem_of_mem_erase hq) (ne_of_mem_erase hq) ψ.1 ψ.2
  have hB := finsum_sub_le (fun ψ : {ψ : DirichletCharacter ℂ r // ψ.IsPrimitive} => F r ψ.1)
    (fun ψ => G r ψ.1) ⟨χ₀, hχ₀⟩ (fun ψ hψ => h2 ψ.1 ψ.2 (fun he => hψ (Subtype.ext he)))
  simp only at hB
  linarith

/-! ### The leaf -/

/-- LEAF: P0015 Lemma 4.3, pages 357 and 358, in the exceptional case, class HARD, CITED: Gallagher
1970 Theorem 7 with MV's two modifications. For each zero free constant `a > 0` there are
`c₃, B > 0` and a range `θ < θ₁`, MV's `P ≤ N^{c₄}` with `c₄` small and absolute, such that, with
`P = X^θ` and `P ≥ P₀(θ)`, which gives MV's `P ≥ exp(log^{1/2} N)`, if `χ̃` mod `r̃` is the
exceptional character with zero `β̃` then there are bounds `M q ψ` for the maxima of
`(h + X/P)⁻¹ |Σ^#|` over `x ≤ 2X`, `0 < h ≤ X`, where for `χ̃` the `Σ^#` is the exceptional
`Σ χ̃(p) log p + Σ n^{β̃-1}`, and `Σ_{q≤P} Σ*_ψ M q ψ ≪ (1-β̃) log P exp(-c₃ log X / log P)`,
"the right hand side of (4.2) may be reduced by a factor of `(1-β̃) log P`". Here
`log X / log P = 1/θ`. -/
theorem mv_gallagher_lemma43_tilde : ∀ a : ℝ, 0 < a → ∃ c₃ B θ₁ : ℝ, 0 < c₃ ∧ 0 < B ∧ 0 < θ₁ ∧
    ∀ θ : ℝ, 0 < θ → θ < θ₁ → ∃ P₀ : ℝ, ∀ X : ℝ, 0 < X → P₀ ≤ X ^ θ →
    ∀ r : ℕ, 1 ≤ r → r ≠ 1 → (r : ℝ) ≤ X ^ θ → SelectedRealZero a (X ^ θ) r →
    ∀ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 1 - a / Real.log (X ^ θ) ≤ β → β < 1 →
      χ.LFunction β = 0 →
      ∃ M : (q : ℕ) → DirichletCharacter ℂ q → ℝ,
        (∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ X ^ θ → q ≠ r → ∀ ψ : DirichletCharacter ℂ q,
          ψ.IsPrimitive → ∀ x h : ℝ, 0 ≤ x → x ≤ 2 * X → 0 < h → h ≤ X →
            ‖sharpSum (X ^ θ) X ψ x h‖ ≤ M q ψ * (h + X / X ^ θ)) ∧
        (∀ ψ : DirichletCharacter ℂ r, ψ.IsPrimitive → ψ ≠ χ →
          ∀ x h : ℝ, 0 ≤ x → x ≤ 2 * X → 0 < h → h ≤ X →
            ‖sharpSum (X ^ θ) X ψ x h‖ ≤ M r ψ * (h + X / X ^ θ)) ∧
        (∀ x h : ℝ, 0 ≤ x → x ≤ 2 * X → 0 < h → h ≤ X →
            ‖sharpSumTilde β (X ^ θ) X χ x h‖ ≤ M r χ * (h + X / X ^ θ)) ∧
        ∑ q ∈ Icc 1 ⌊X ^ θ⌋₊, ∑ᶠ ψ : {ψ : DirichletCharacter ℂ q // ψ.IsPrimitive}, M q ψ.1 ≤
          B * (1 - β) * Real.log (X ^ θ) * Real.exp (-(c₃ / θ)) := by
  sorry

/-! ### The faithful twin of `mv_71_tilde`, PROVED from the leaf -/

/-- P0015 display (7.1̃), page 366, in the range MV prove it: for each `a > 0` there is `θ₁ > 0`
such that for `θ < θ₁`, `W ≪ X^{1/2} (1 - β̃) exp(-c₆ log X / log P) log P`, `log X / log P = 1/θ`.
Same hypotheses and conclusion as `Lemma3MVSplit.mv_71_tilde`, with `θ < θ₁` for `θ < 6/100`.
PROVED from the leaf `mv_gallagher_lemma43_tilde` and the proved Lemma 4.2 steps. -/
theorem mv_71_tilde_small : ∀ a : ℝ, 0 < a → ∃ θ₁ : ℝ, 0 < θ₁ ∧ ∃ B c₆ : ℝ, 0 < B ∧ 0 < c₆ ∧
    ∀ θ : ℝ, 0 < θ → θ < θ₁ → ∃ P₀ : ℝ, ∀ X : ℝ, 0 < X → P₀ ≤ X ^ θ →
    ∀ r : ℕ, 1 ≤ r → r ≠ 1 → (r : ℝ) ≤ X ^ θ → SelectedRealZero a (X ^ θ) r →
    ∀ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 1 - a / Real.log (X ^ θ) ≤ β → β < 1 →
      χ.LFunction β = 0 →
        |mvWtilde β (X ^ θ) X χ| ≤
          B * Real.sqrt X * (1 - β) * Real.exp (-(c₆ / θ)) * Real.log (X ^ θ) := by
  intro a ha
  obtain ⟨C, hC, hG⟩ := mv_gallagher_lemma42_step
  obtain ⟨c₃, B, θ₁, hc₃, hB, hθ₁, hL⟩ := mv_gallagher_lemma43_tilde a ha
  set K := max C 49 with hK
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨min θ₁ (6 / 100), lt_min hθ₁ (by norm_num), K * B, c₃, by positivity, hc₃, ?_⟩
  intro θ hθ hθm
  have hθa : θ < θ₁ := lt_of_lt_of_le hθm (min_le_left _ _)
  have hθb : θ < 6 / 100 := lt_of_lt_of_le hθm (min_le_right _ _)
  obtain ⟨X₀, hX₀⟩ := hG (θ / 6) (by positivity) (by linarith)
  have e6 : 6 * (θ / 6) = θ := by ring
  rw [e6] at hX₀
  obtain ⟨PL, hPL⟩ := hL θ hθ hθa
  refine ⟨max PL ((max X₀ 256) ^ θ), ?_⟩
  intro X hX hP r hr1 hr1' hrP hsel hNZ χ β hprim hsq hne hβ hβ1 hLz
  have hPL' : PL ≤ X ^ θ := le_trans (le_max_left _ _) hP
  have hXX : max X₀ 256 ≤ X := by
    have h := le_trans (le_max_right _ _) hP
    exact (Real.rpow_le_rpow_iff (le_trans (by norm_num) (le_max_right _ _)) hX.le hθ).mp h
  have hX256 : 256 ≤ X := le_trans (le_max_right _ _) hXX
  have hXX₀ : X₀ ≤ X := le_trans (le_max_left _ _) hXX
  obtain ⟨M, hM1, hM2, hM3, hMs⟩ :=
    hPL X hX hPL' r hr1 hr1' hrP hsel hNZ χ β hprim hsq hne hβ hβ1 hLz
  set P := X ^ θ with hPdef
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hP0 : 0 < P := Real.rpow_pos_of_pos hX _
  have hsX : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hrmem : r ∈ Icc 1 ⌊P⌋₊ := mem_Icc.mpr ⟨hr1, Nat.le_floor hrP⟩
  have hqP : ∀ q ∈ Icc 1 ⌊P⌋₊, 1 ≤ q ∧ (q : ℝ) ≤ P := fun q hq =>
    ⟨(mem_Icc.mp hq).1, le_trans (by exact_mod_cast (mem_Icc.mp hq).2) (Nat.floor_le hP0.le)⟩
  -- each non exceptional summand, by the reused proved Lemma 4.2 step
  have hW : ∀ (q : ℕ) (ψ : DirichletCharacter ℂ q), 1 ≤ q → (q : ℝ) ≤ P → ψ.IsPrimitive →
      (∀ x h : ℝ, 0 ≤ x → x ≤ 2 * X → 0 < h → h ≤ X →
        ‖sharpSum P X ψ x h‖ ≤ M q ψ * (h + X / P)) →
      Wnorm P X ψ ≤ K * Real.sqrt X * M q ψ := by
    intro q ψ hq1 hqP' hψ hb
    have hM0 : 0 ≤ M q ψ := bound_nonneg _ _ X P hX hP0
      (by simpa using hb 0 1 le_rfl (by linarith) one_pos hX1)
    have h1 := hX₀ X hXX₀ q hq1 hqP' ψ hψ (M q ψ) hb
    have h2 : C * Real.sqrt X * M q ψ ≤ K * Real.sqrt X * M q ψ := by
      have := mul_nonneg hsX hM0
      nlinarith [le_max_left C 49]
    linarith
  have hT0 : 0 ≤ M r χ := bound_nonneg _ _ X P hX hP0
    (by simpa using hM3 0 1 le_rfl (by linarith) one_pos hX1)
  have hT : WnormTilde β P X χ ≤ K * Real.sqrt X * M r χ := by
    have h1 := wnormTilde_le β θ X hθ (by linarith) hX256 hr1 hrP χ hne (M r χ) hM3
    have := mul_nonneg hsX hT0
    nlinarith [le_max_right C 49]
  -- surgery: the non exceptional part of `W`
  have hup := sum_sub_le ⌊P⌋₊ r hrmem (fun q ψ => Wnorm P X ψ)
    (fun q ψ => K * Real.sqrt X * M q ψ) χ hprim
    (fun q hq hqr ψ hψ => hW q ψ (hqP q hq).1 (hqP q hq).2 hψ
      (hM1 q (hqP q hq).1 (hqP q hq).2 hqr ψ hψ))
    (fun ψ hψ hψχ => hW r ψ hr1 hrP hψ (hM2 ψ hψ hψχ))
  have hlow := sum_sub_le ⌊P⌋₊ r hrmem (fun _ _ => (0 : ℝ)) (fun q ψ => Wnorm P X ψ) χ hprim
    (fun _ _ _ ψ _ => Real.sqrt_nonneg _) (fun ψ _ _ => Real.sqrt_nonneg _)
  simp only [finsum_zero, sum_const_zero, sub_zero] at hlow hup
  have hfac : ∀ q, ∑ᶠ ψ : {ψ : DirichletCharacter ℂ q // ψ.IsPrimitive},
      K * Real.sqrt X * M q ψ.1 = K * Real.sqrt X *
        ∑ᶠ ψ : {ψ : DirichletCharacter ℂ q // ψ.IsPrimitive}, M q ψ.1 := fun q => by
    rw [mul_finsum]
  simp only [hfac, ← mul_sum] at hup
  have hWdef : mvWtilde β P X χ = (mvW P X - Wnorm P X χ) + WnormTilde β P X χ := by
    unfold mvWtilde; ring
  have hmvW : mvW P X = ∑ q ∈ Icc 1 ⌊P⌋₊,
      ∑ᶠ ψ : {ψ : DirichletCharacter ℂ q // ψ.IsPrimitive}, Wnorm P X ψ.1 := rfl
  have hTn : 0 ≤ WnormTilde β P X χ := Real.sqrt_nonneg _
  have hnn : 0 ≤ mvWtilde β P X χ := by rw [hWdef, hmvW]; linarith
  have hfin : mvWtilde β P X χ ≤
      K * Real.sqrt X * (B * (1 - β) * Real.log P * Real.exp (-(c₃ / θ))) := by
    have hKs : 0 ≤ K * Real.sqrt X := by positivity
    have := mul_le_mul_of_nonneg_left hMs hKs
    rw [hWdef, hmvW]; linarith
  rw [abs_of_nonneg hnn]
  calc _ ≤ _ := hfin
    _ = K * B * Real.sqrt X * (1 - β) * Real.exp (-(c₃ / θ)) * Real.log P := by ring

/-- Sanity twin: the reviewed leaf `mv_71_tilde` implies the repaired `mv_71_tilde_small`, so the
repair is weaker. PROVED. -/
theorem mv_71_tilde_small_of_old (h : type_of% @mv_71_tilde) :
    type_of% @mv_71_tilde_small := by
  intro a ha
  obtain ⟨B, c₆, hB, hc₆, hW⟩ := h a ha
  exact ⟨6 / 100, by norm_num, B, c₆, hB, hc₆, hW⟩

/-! ### P0082 Lemma 3 for small `θ`, PROVED from the leaves -/

/-- P0082 page 358 Lemma 3, the shape of `BPLemma3Hyp`, with `θ` restricted to `(0, θ₁)` for some
`θ₁ > 0` depending on `a`, the range in which MV prove (7.1̃). PROVED from
`Lemma3MVSplit.mv_617_tilde`, the twin `mv_71_tilde_small` and `Lemma3MVSplit.w_terms_le`. -/
theorem bpLemma3HypSmall_of_leaves : ∀ a : ℝ, 0 < a → ∃ θ₁ : ℝ, 0 < θ₁ ∧ ∃ C c₂ : ℝ,
    0 < C ∧ 0 < c₂ ∧
    ∀ θ : ℝ, 0 < θ → θ < θ₁ → ∃ P₀ : ℝ, ∀ X : ℝ, 0 < X → P₀ ≤ X ^ θ →
    ∀ r : ℕ, 1 ≤ r → r ≠ 1 → (r : ℝ) ≤ X ^ θ → SelectedRealZero a (X ^ θ) r →
    ∀ (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
      χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 → 1 - a / Real.log (X ^ θ) ≤ β → β < 1 →
      χ.LFunction β = 0 →
      ∀ m : ℤ, 1 ≤ m → (m : ℝ) ≤ X → Even m →
        |(R1 (X ^ θ) X m).re - (m * singSeries m + Itilde β (X ^ θ) m * twistedSing χ m)| ≤
          C * X * divisorError r (X ^ θ) m +
          C * X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 *
            ((m.toNat : ℝ) / (m.toNat.totient : ℝ)) +
          C * X * ((m.toNat : ℝ) / (m.toNat.totient : ℝ)) * (1 - β) *
            Real.exp (-(c₂ / θ)) * Real.log (X ^ θ) := by
  intro a ha
  obtain ⟨CA, hCA, hA⟩ := mv_617_tilde a ha
  obtain ⟨θ₁, hθ₁, B, c₆, hB, hc₆, hW⟩ := mv_71_tilde_small a ha
  refine ⟨min θ₁ (6 / 100), lt_min hθ₁ (by norm_num),
    CA * (1 + B + B ^ 2 * a), c₆, by positivity, hc₆, ?_⟩
  intro θ hθ hθm
  obtain ⟨PA, hPA⟩ := hA θ hθ (lt_of_lt_of_le hθm (min_le_right _ _))
  obtain ⟨PB, hPB⟩ := hW θ hθ (lt_of_lt_of_le hθm (min_le_left _ _))
  refine ⟨max (max PA PB) 2, ?_⟩
  intro X hX hP r hr1 hr1' hrP hsel hNZ χ β hprim hsq hne hβ hβ1 hL m hm1 hmX hev
  have hPA' : PA ≤ X ^ θ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hP
  have hPB' : PB ≤ X ^ θ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hP
  have hP2 : (2 : ℝ) ≤ X ^ θ := le_trans (le_max_right _ _) hP
  have hlogP : 0 < Real.log (X ^ θ) := Real.log_pos (by linarith)
  have hA1 := hPA X hX hPA' r hr1 hr1' hrP hsel hNZ χ β hprim hsq hne hβ hβ1 hL m hm1 hmX hev
  have hW1 := hPB X hX hPB' r hr1 hr1' hrP hsel hNZ χ β hprim hsq hne hβ hβ1 hL
  set P := X ^ θ with hPdef
  set W := mvWtilde β P X χ
  set M := (m.toNat : ℝ) / (m.toNat.totient : ℝ)
  set u := (1 - β) * Real.log P with hu
  set e := Real.exp (-(c₆ / θ)) with he
  have hu0 : 0 ≤ u := mul_nonneg (by linarith) hlogP.le
  have hua : u ≤ a := by
    have h1 : 1 - β ≤ a / Real.log P := by linarith
    exact (le_div_iff₀ hlogP).mp h1
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have he1 : e ≤ 1 := by
    rw [he, Real.exp_le_one_iff]; exact neg_nonpos.mpr (div_nonneg hc₆.le hθ.le)
  have hW2 : |W| ≤ B * Real.sqrt X * (u * e) := by
    have : B * Real.sqrt X * (1 - β) * e * Real.log P = B * Real.sqrt X * (u * e) := by
      rw [hu]; ring
    rw [← this]; exact hW1
  have hterms := w_terms_le W B X u e a hB.le hX.le hu0 hua he0 he1 hW2
  have hM : 0 ≤ M := by positivity
  have hD : 0 ≤ divisorError r P m := by
    unfold divisorError
    apply add_nonneg
    · apply mul_nonneg (by positivity)
      exact sum_nonneg (fun q _ => by positivity)
    · apply mul_nonneg (by positivity)
      exact tsum_nonneg (fun q => by split_ifs <;> positivity)
  have hchi : 0 ≤ X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M := by positivity
  have hk : 1 ≤ 1 + B + B ^ 2 * a := by
    have := mul_nonneg (sq_nonneg B) ha.le; linarith
  have hCk : CA ≤ CA * (1 + B + B ^ 2 * a) := le_mul_of_one_le_right hCA.le hk
  have hfin : CA * M * (W * Real.sqrt X + W ^ 2) ≤
      CA * (1 + B + B ^ 2 * a) * X * M * (1 - β) * e * Real.log P := by
    have h1 : CA * M * (W * Real.sqrt X + W ^ 2) ≤ CA * M * ((B + B ^ 2 * a) * X * (u * e)) :=
      mul_le_mul_of_nonneg_left hterms (by positivity)
    have h2 : CA * M * ((B + B ^ 2 * a) * X * (u * e)) ≤
        CA * (1 + B + B ^ 2 * a) * X * M * (u * e) := by
      have hY : 0 ≤ CA * X * M * (u * e) := by positivity
      calc CA * M * ((B + B ^ 2 * a) * X * (u * e)) =
            (B + B ^ 2 * a) * (CA * X * M * (u * e)) := by ring
        _ ≤ (1 + B + B ^ 2 * a) * (CA * X * M * (u * e)) :=
            mul_le_mul_of_nonneg_right (by linarith) hY
        _ = CA * (1 + B + B ^ 2 * a) * X * M * (u * e) := by ring
    calc CA * M * (W * Real.sqrt X + W ^ 2) ≤ CA * (1 + B + B ^ 2 * a) * X * M * (u * e) :=
          h1.trans h2
      _ = CA * (1 + B + B ^ 2 * a) * X * M * (1 - β) * e * Real.log P := by rw [hu]; ring
  have hXD : CA * X * divisorError r P m ≤
      CA * (1 + B + B ^ 2 * a) * X * divisorError r P m := by
    have h0 : 0 ≤ X * divisorError r P m := mul_nonneg hX.le hD
    calc CA * X * divisorError r P m = CA * (X * divisorError r P m) := by ring
      _ ≤ CA * (1 + B + B ^ 2 * a) * (X * divisorError r P m) :=
          mul_le_mul_of_nonneg_right hCk h0
      _ = CA * (1 + B + B ^ 2 * a) * X * divisorError r P m := by ring
  have hXc : CA * X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M ≤
      CA * (1 + B + B ^ 2 * a) * X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) /
        (r.totient : ℝ) ^ 2 * M := by
    have e1 : CA * X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M =
        CA * (X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M) := by ring
    have e2 : CA * (1 + B + B ^ 2 * a) * X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) /
        (r.totient : ℝ) ^ 2 * M =
        CA * (1 + B + B ^ 2 * a) *
          (X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M) := by
      ring
    rw [e1, e2]; exact mul_le_mul_of_nonneg_right hCk hchi
  calc _ ≤ _ := hA1
    _ ≤ _ := by
      have : CA * X * M * (1 - β) * e * Real.log P =
          CA * X * M * (1 - β) * Real.exp (-(c₆ / θ)) * Real.log P := by rw [he]
      linarith [hfin, hXD, hXc]

/-- Sanity twin: `BPLemma3Hyp` implies the small `θ` form, so the latter is weaker. PROVED. -/
theorem bpLemma3HypSmall_of_BP (h : BPLemma3Hyp) : type_of% @bpLemma3HypSmall_of_leaves := by
  intro a ha
  obtain ⟨C, c₂, hC, hc₂, hW⟩ := h a ha
  exact ⟨6 / 100, by norm_num, C, c₂, hC, hc₂, hW⟩

end LeanLab.ExceptionalSet.UpJ200.Lemma3MV71Repair

#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma3MV71Repair.mv_71_tilde_small
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma3MV71Repair.bpLemma3HypSmall_of_leaves
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma3MV71Repair.wnormTilde_le
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma3MV71Repair.mv_71_tilde_small_of_old
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma3MV71Repair.bpLemma3HypSmall_of_BP
