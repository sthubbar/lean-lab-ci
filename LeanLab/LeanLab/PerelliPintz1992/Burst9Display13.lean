/-
P0070. A. Perelli and J. Pintz, On the exceptional set for the 2k-twin primes problem,
Compositio Math. 82, 1992, pp. 355 to 372. Display 13, p. 361, the character expansion of
`R(η, q, a) = S(a/q + η) - μ(q)/φ(q) T(η)`:
`R(η, q, a) = φ(q)^{-1} Σ_χ χ̄(a) τ(χ) Ψ'(χ̄, η) + O(N^{1/2})`,
with `Ψ'(χ, η) = Σ_n (Λ(n) χ(n) - δ_χ) e(nη)` and `δ_χ = 1` for the principal character.

ROUTE BURST session 9, 2026-11-12. All proved here, for an arbitrary finite set `I` of
summation indices, since the dyadic step of p. 364 is done here with the range `[N, 2N]`
replaced by subranges, see `Burst9Rpart.lean`:

* `gauss_one_eq_moebius`: `τ(χ₀) = μ(q)`, from Ramanujan's sum `ramanujan_coprime`.
* `char_expand_e`: `e(m/q) = φ(q)^{-1} Σ_χ χ̄(m) τ(χ)` for a reduced residue `m`, by the
  orthogonality of the characters.
* `display13`: the exact identity `R = φ(q)^{-1} Σ_χ χ̄(a) τ(χ) Ψ'(χ̄) + E`, where `E` is the
  sum of `Λ(n) e(n(a/q + η))` over the `n` with `(n, q) > 1`, the `O(N^{1/2})` of display 13.
* `norm_gaussSum_inv`: `|τ(χ̄)| = |τ(χ)|`.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.PerelliPintz1992.Decomp1519

namespace LeanLab.PerelliPintz1992.Burst9
open Real ArithmeticFunction MeasureTheory Set Filter Topology
open LeanLab.PerelliPintz1992 LeanLab.PerelliPintz1992.Decomp1519

noncomputable section
attribute [local instance] Classical.propDecidable

/-! ### Definitions over an index set `I` -/

/-- The coefficient `Λ(n) χ(n) - δ_χ` of `Ψ'`, display 13, p. 361; it is the summand of
`Decomp1624.movingSum`. -/
def cf {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) (n : ℕ) : ℂ :=
  (Λ n : ℂ) * χ (n : ZMod (q : ℕ)) - if χ = 1 then 1 else 0

/-- `S` over the index set `I`: `Σ_{n ∈ I} Λ(n) e(nα)`. -/
def Sx (I : Finset ℕ) (α : ℝ) : ℂ := ∑ n ∈ I, (Λ n : ℂ) * e (n * α)

/-- `T` over the index set `I`: `Σ_{n ∈ I} e(nη)`. -/
def Tx (I : Finset ℕ) (η : ℝ) : ℂ := ∑ n ∈ I, e (n * η)

/-- `R` over the index set `I`: `S(a/q + η) - μ(q)/φ(q) T(η)`, p. 357. -/
def Rx (I : Finset ℕ) (q a : ℕ) (η : ℝ) : ℂ :=
  Sx I ((a : ℝ) / q + η) - (muφ q : ℂ) * Tx I η

/-- `Ψ'(χ, η) = Σ_{n ∈ I} (Λ(n) χ(n) - δ_χ) e(nη)`, display 13. -/
def Psx (I : Finset ℕ) {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) (η : ℝ) : ℂ :=
  ∑ n ∈ I, cf χ n * e (n * η)

/-- The terms with `(n, q) > 1`, the `O(N^{1/2})` of display 13. -/
def Ex (I : Finset ℕ) (q a : ℕ) (η : ℝ) : ℂ :=
  ∑ n ∈ I.filter (fun n => ¬ Nat.Coprime n q), (Λ n : ℂ) * e (n * ((a : ℝ) / q + η))

/-- With `I = [N, 2N]` the index set form is the paper's `R`. PROVED. -/
theorem Rx_Icc (N q a : ℕ) (η : ℝ) : Rx (Finset.Icc N (2 * N)) q a η = R N q a η := rfl

/-- `R` is additive in the index set. PROVED. -/
theorem Rx_union (I J : Finset ℕ) (h : Disjoint I J) (q a : ℕ) (η : ℝ) :
    Rx (I ∪ J) q a η = Rx I q a η + Rx J q a η := by
  unfold Rx Sx Tx
  rw [Finset.sum_union h, Finset.sum_union h]
  ring

/-! ### Sums over `ZMod q` -/

/-- A sum over `ZMod q` is the sum over the representatives `0 ≤ b < q`. PROVED. -/
theorem sum_zmod_eq_range (q : ℕ+) (f : ZMod (q : ℕ) → ℂ) :
    ∑ x : ZMod (q : ℕ), f x = ∑ b ∈ Finset.range (q : ℕ), f (b : ZMod (q : ℕ)) := by
  refine Finset.sum_nbij' (fun x => x.val) (fun b => (b : ZMod (q : ℕ))) ?_ ?_ ?_ ?_ ?_
  · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt x)
  · intro b _; exact Finset.mem_univ _
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro b hb; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hb)
  · intro x _; rw [ZMod.natCast_zmod_val]

/-- The standard additive character at an integer residue is `e(j/q)`. PROVED. -/
theorem stdAddChar_natCast (q : ℕ+) (j : ℕ) :
    (ZMod.stdAddChar (j : ZMod (q : ℕ)) : ℂ) = e ((j : ℝ) / (q : ℕ)) := by
  have h := ZMod.stdAddChar_coe (N := (q : ℕ)) (j : ℤ)
  simp only [Int.cast_natCast] at h
  rw [h]
  unfold e
  congr 1
  push_cast
  ring

/-- `τ(χ₀) = μ(q)`, Ramanujan's sum at `1`, p. 361. PROVED. -/
theorem gauss_one_eq_moebius (q : ℕ+) :
    gaussSum (1 : DirichletCharacter ℂ (q : ℕ)) ZMod.stdAddChar =
      ((ArithmeticFunction.moebius (q : ℕ) : ℤ) : ℂ) := by
  unfold gaussSum
  rw [sum_zmod_eq_range q]
  have h := ramanujan_coprime (q := (q : ℕ)) (a := 1) q.pos (Nat.coprime_one_left _)
  rw [← h, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : Nat.Coprime b q
  · have hu : IsUnit (b : ZMod (q : ℕ)) := (ZMod.isUnit_iff_coprime b q).mpr hb
    rw [if_pos hb, MulChar.one_apply hu, one_mul, stdAddChar_natCast]
    congr 1; push_cast; ring
  · have hu : ¬ IsUnit (b : ZMod (q : ℕ)) := fun h => hb ((ZMod.isUnit_iff_coprime b q).mp h)
    rw [if_neg hb, MulChar.map_nonunit _ hu, zero_mul]

/-- `χ̄(m) = χ(m⁻¹)` at a unit. PROVED. -/
theorem inv_apply_unit {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) {m : ZMod (q : ℕ)}
    (hm : IsUnit m) : χ⁻¹ m = χ m⁻¹ := by
  have h1 : χ⁻¹ m * χ m = 1 := by
    rw [← MulChar.mul_apply, MulChar.inv_mul, MulChar.one_apply hm]
  have h2 : χ m⁻¹ * χ m = 1 := by
    rw [← map_mul, ZMod.inv_mul_of_unit m hm, map_one]
  have h3 : χ m ≠ 0 := by
    intro h; rw [h, mul_zero] at h1; exact zero_ne_one h1
  exact mul_right_cancel₀ h3 (h1.trans h2.symm)

/-- **The character expansion of `e(m/q)`**, p. 361: for a reduced residue `m`,
`Σ_χ χ̄(m) τ(χ) = φ(q) e(m/q)`; for `m` not a unit every `χ̄(m)` vanishes. PROVED. -/
theorem char_expand_e (q : ℕ+) {m : ZMod (q : ℕ)} (hm : IsUnit m) :
    ∑ χ : DirichletCharacter ℂ (q : ℕ), χ⁻¹ m * gaussSum χ ZMod.stdAddChar =
      (Nat.totient (q : ℕ) : ℂ) * ZMod.stdAddChar m := by
  unfold gaussSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have key : ∀ x : ZMod (q : ℕ), ∑ χ : DirichletCharacter ℂ (q : ℕ),
      χ⁻¹ m * (χ x * ZMod.stdAddChar x) =
        (if m = x then (Nat.totient (q : ℕ) : ℂ) else 0) * ZMod.stdAddChar x := by
    intro x
    rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ hm x, Finset.sum_mul]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [inv_apply_unit χ hm]; ring
  simp_rw [key]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem char_expand_e_nonunit (q : ℕ+) {m : ZMod (q : ℕ)} (hm : ¬ IsUnit m) :
    ∑ χ : DirichletCharacter ℂ (q : ℕ), χ⁻¹ m * gaussSum χ ZMod.stdAddChar = 0 := by
  refine Finset.sum_eq_zero fun χ _ => ?_
  rw [MulChar.map_nonunit _ hm, zero_mul]

/-- **Display 13, p. 361**, exactly: for `(a, q) = 1`,
`R(η, q, a) = φ(q)^{-1} Σ_χ χ̄(a) τ(χ) Ψ'(χ̄, η) + E(η)`, `E` the terms with `(n, q) > 1`.
PROVED. -/
theorem display13 (I : Finset ℕ) (q : ℕ+) {a : ℕ} (ha : Nat.Coprime a q) (η : ℝ) :
    Rx I q a η = (1 / (Nat.totient (q : ℕ) : ℂ)) *
        ∑ χ : DirichletCharacter ℂ (q : ℕ),
          χ⁻¹ (a : ZMod (q : ℕ)) * gaussSum χ ZMod.stdAddChar * Psx I χ⁻¹ η +
      Ex I q a η := by
  have hφ : (Nat.totient (q : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr q.pos).ne'
  have hau : IsUnit (a : ZMod (q : ℕ)) := (ZMod.isUnit_iff_coprime a q).mpr ha
  -- expand `Ψ'` and swap the sums
  have hexp : ∑ χ : DirichletCharacter ℂ (q : ℕ),
      χ⁻¹ (a : ZMod (q : ℕ)) * gaussSum χ ZMod.stdAddChar * Psx I χ⁻¹ η =
      ∑ n ∈ I, ((Λ n : ℂ) * e (n * η) * ∑ χ : DirichletCharacter ℂ (q : ℕ),
          χ⁻¹ ((a * n : ℕ) : ZMod (q : ℕ)) * gaussSum χ ZMod.stdAddChar) -
        (∑ χ : DirichletCharacter ℂ (q : ℕ), χ⁻¹ (a : ZMod (q : ℕ)) *
          gaussSum χ ZMod.stdAddChar * (if χ⁻¹ = 1 then 1 else 0)) * Tx I η := by
    unfold Psx cf Tx
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun χ _ => ?_
    push_cast
    rw [map_mul]
    ring
  -- the principal term
  have hprin : (∑ χ : DirichletCharacter ℂ (q : ℕ), χ⁻¹ (a : ZMod (q : ℕ)) *
      gaussSum χ ZMod.stdAddChar * (if χ⁻¹ = 1 then 1 else 0)) =
      ((ArithmeticFunction.moebius (q : ℕ) : ℤ) : ℂ) := by
    have hiff : ∀ χ : DirichletCharacter ℂ (q : ℕ), (χ⁻¹ = 1) ↔ (χ = 1) := fun χ => inv_eq_one
    simp_rw [hiff, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ (1 : DirichletCharacter ℂ (q : ℕ)), if_pos (Finset.mem_univ _),
      inv_one, MulChar.one_apply hau, one_mul, gauss_one_eq_moebius]
  -- the coprime terms
  have hterm : ∀ n ∈ I, (Λ n : ℂ) * e (n * η) * ∑ χ : DirichletCharacter ℂ (q : ℕ),
      χ⁻¹ ((a * n : ℕ) : ZMod (q : ℕ)) * gaussSum χ ZMod.stdAddChar =
      (Nat.totient (q : ℕ) : ℂ) *
        (if Nat.Coprime n q then (Λ n : ℂ) * e (n * ((a : ℝ) / q + η)) else 0) := by
    intro n _
    by_cases hn : Nat.Coprime n q
    · have hu : IsUnit ((a * n : ℕ) : ZMod (q : ℕ)) :=
        (ZMod.isUnit_iff_coprime _ _).mpr (Nat.coprime_mul_iff_left.mpr ⟨ha, hn⟩)
      rw [char_expand_e q hu, stdAddChar_natCast, if_pos hn]
      have : e (n * ((a : ℝ) / q + η)) = e (((a * n : ℕ) : ℝ) / (q : ℕ)) * e (n * η) := by
        rw [← e_add]; congr 1; push_cast; ring
      rw [this]; ring
    · have hu : ¬ IsUnit ((a * n : ℕ) : ZMod (q : ℕ)) := by
        rw [ZMod.isUnit_iff_coprime]
        intro h; exact hn (Nat.Coprime.coprime_mul_left h)
      rw [char_expand_e_nonunit q hu, if_neg hn]; ring
  rw [hexp, hprin, Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  unfold Rx Sx Ex muφ
  have hsplit : ∑ n ∈ I, (Λ n : ℂ) * e (n * ((a : ℝ) / q + η)) =
      (∑ n ∈ I, if Nat.Coprime n q then (Λ n : ℂ) * e (n * ((a : ℝ) / q + η)) else 0) +
        ∑ n ∈ I.filter (fun n => ¬ Nat.Coprime n q), (Λ n : ℂ) * e (n * ((a : ℝ) / q + η)) := by
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : Nat.Coprime n q <;> simp [hn]
  rw [hsplit, mul_sub, ← mul_assoc, one_div_mul_cancel hφ, one_mul]
  push_cast
  ring

/-- `|τ(χ̄)| = |τ(χ)|`, from `star_gaussSum_eq` and the shift by `-1`. PROVED. -/
theorem norm_gaussSum_inv {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) :
    ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ = ‖gaussSum χ ZMod.stdAddChar‖ := by
  have h1 := star_gaussSum_eq χ (ZMod.stdAddChar (N := (q : ℕ)))
  have h2 := gaussSum_mulShift χ⁻¹ (ZMod.stdAddChar (N := (q : ℕ))) (-1)
  simp only [Units.val_neg, Units.val_one] at h2
  rw [← AddChar.inv_mulShift] at h2
  have hn : ‖χ⁻¹ (-1 : ZMod (q : ℕ))‖ = 1 := by
    set z := χ⁻¹ (-1 : ZMod (q : ℕ))
    have hz : z ^ 2 = 1 := by
      simp only [z]; rw [← map_pow, neg_one_sq, map_one]
    have : ‖z‖ ^ 2 = 1 := by rw [← norm_pow, hz, norm_one]
    have h0 : 0 ≤ ‖z‖ := norm_nonneg _
    nlinarith
  rw [← h2, norm_mul, hn, one_mul, ← h1, norm_star]

/-- `|τ(χ)| ≤ q`. PROVED. -/
theorem norm_gaussSum_le {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) :
    ‖gaussSum χ ZMod.stdAddChar‖ ≤ (q : ℕ) := by
  unfold gaussSum
  refine (norm_sum_le _ _).trans ?_
  have : ∀ x : ZMod (q : ℕ), ‖χ x * (ZMod.stdAddChar x : ℂ)‖ ≤ 1 := by
    intro x
    rw [norm_mul]
    have h1 : ‖χ x‖ ≤ 1 := DirichletCharacter.norm_le_one χ x
    have h2 : ‖(ZMod.stdAddChar x : ℂ)‖ = 1 := by
      rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
    rw [h2, mul_one]; exact h1
  refine (Finset.sum_le_sum fun x _ => this x).trans ?_
  simp [ZMod.card]

/-- The number of characters is `φ(q)`. PROVED. -/
theorem card_chars (q : ℕ+) :
    (Fintype.card (DirichletCharacter ℂ (q : ℕ)) : ℝ) = Nat.totient (q : ℕ) := by
  rw [← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ (q : ℕ)]

#print axioms Rx_union
#print axioms sum_zmod_eq_range
#print axioms gauss_one_eq_moebius
#print axioms char_expand_e
#print axioms display13
#print axioms norm_gaussSum_inv
#print axioms norm_gaussSum_le
#print axioms card_chars

end
end LeanLab.PerelliPintz1992.Burst9
