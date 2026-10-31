/-
AI wrote this Lean code. Claude, for the Lean Lab, PC run 20261029T0804Z-25466, unit U-1585,
T2 FRONTIER, the Goldbach exceptional set exponent, idea I-0139, a follow-up of I-0133.

Question: can the non-cube-free moduli be split off, so that Heath-Brown's cube-free
`ϕ = 1/4` (1992, Lemma 2.5, p. 10) suffices in Zhao's method, arXiv 2511.05631?

Where the moduli come from.  Pintz 2018, arXiv 1804.09084, pp. 6 to 8: the even `m` are split
into at most `2^K` classes `M(R')`, (2.26), by the subset `R'` of the boundedly many generalised
exceptional zeros whose conductors `r_i` divide `C₁ m`; the class modulus is
`q = q(R') = lcm [r_i ; r_i ∈ R']`, (2.27).  Classes with `q > X^ϑ` have `|M(R')| ≪ X^{1-ϑ}`,
(2.28) and (2.29); every other class needs (2.33) for that one `q`, with `A = log X / log q`.
Theorems C, H, I need `ϕ ≥ max_{χ mod q} ϕ(χ)`, (4.1) p. 12 and p. 16, and the proof of
Theorem C applies Lemma 2.5 to the zero's own `χ` and to `χ_i χ̄_j`, both mod `q`, (5.10) p. 21 and
(5.16) p. 22.  Zhao fixes `ϕ = 1/3` after his (2.7) and quotes the same single-modulus reduction.

Answer, NEGATIVE.  The lcm of cube-free numbers is cube-free, `cubeFree_lcm`, so a class with
cube-free `q(R')` needs only `ϕ = 1/4`.  But `q(R')` is fixed by the hypothetical zeros, not chosen,
and a non-cube-free class is not negligible: its size is `≍ X/q`, set by the size of `q` and not by
its arithmetic.  A single non-cube-free class with `q = X^θ`, `θ` just above `1/W*(1/3) ≈ 0.3003`,
fails to close at `ϕ = 1/3` and costs `X^{1-θ} ≈ X^{0.6997}`.  So the split gives back Zhao's 7/10,
`split_gives_zhao`, and the exponent below 7/10 still needs Lemma 2.5 at `ϕ < 1/3` on NON-CUBE-FREE
moduli, `BurgessPhiOn NonCubeFree`, which is OPEN.  `target_of_split` records exactly this.
MODEL numerics: Routes/numerics/U1585/cubefree_split.py.
Binary Goldbach is OPEN; nothing here is progress on it.
-/
import Mathlib
import LeanLab.Routes.U1563Frontier

open Real

noncomputable section
namespace LeanLab.Routes.U1585

open LeanLab.Routes.U1563

/-! ## 1. Cube-free moduli -/

/-- `q` is cube-free: no prime cube divides `q`.  Note `¬ CubeFree 0`. -/
def CubeFree (q : ℕ) : Prop := ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ q

/-- The complement, the moduli Heath-Brown's `ϕ = 1/4` does not reach. -/
def NonCubeFree (q : ℕ) : Prop := ¬ CubeFree q

theorem cubeFree_ne_zero {q : ℕ} (h : CubeFree q) : q ≠ 0 := by
  rintro rfl; exact h 2 Nat.prime_two (dvd_zero _)

/-- A divisor of a cube-free number is cube-free: every character mod a cube-free `q` has
cube-free conductor. -/
theorem cubeFree_of_dvd {d q : ℕ} (hd : d ∣ q) (h : CubeFree q) : CubeFree d :=
  fun p hp hpd => h p hp (hpd.trans hd)

/-- PROVED: the lcm of two cube-free numbers is cube-free.  So Pintz's class modulus
`q(R') = lcm [r_i]`, (2.27), is cube-free when every conductor in `R'` is. -/
theorem cubeFree_lcm {a b : ℕ} (ha : CubeFree a) (hb : CubeFree b) : CubeFree (Nat.lcm a b) := by
  intro p hp hdvd
  have ha0 := cubeFree_ne_zero ha
  have hb0 := cubeFree_ne_zero hb
  have hl0 : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha0 hb0
  have h3 : 3 ≤ (Nat.lcm a b).factorization p := (hp.pow_dvd_iff_le_factorization hl0).mp hdvd
  rw [Nat.factorization_lcm ha0 hb0, Finsupp.sup_apply] at h3
  rcases le_max_iff.mp h3 with h | h
  · exact ha p hp ((hp.pow_dvd_iff_le_factorization ha0).mpr h)
  · exact hb p hp ((hp.pow_dvd_iff_le_factorization hb0).mpr h)

/-- PROVED: the lcm of a finite list of cube-free numbers is cube-free. -/
theorem cubeFree_foldr_lcm (l : List ℕ) (hl : ∀ r ∈ l, CubeFree r) :
    CubeFree (l.foldr Nat.lcm 1) := by
  induction l with
  | nil =>
    intro p hp h
    have h1 := Nat.le_of_dvd Nat.one_pos h
    have h2 : 2 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp.two_le 3
    omega
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact cubeFree_lcm (hl a (by simp)) (ih fun r hr => hl r (by simp [hr]))

/-- Non-cube-free moduli exist: `8 = 2³`.  Their share of `q ≤ N` tends to `1 - 1/ζ(3) ≈ 0.168`. -/
theorem nonCubeFree_eight : NonCubeFree 8 := fun h => h 2 Nat.prime_two (by norm_num)

/-! ## 2. Heath-Brown's Lemma 2.5 on a class of moduli -/

/-- Heath-Brown 1992, Lemma 2.5, for the nonprincipal primitive characters whose modulus lies in
`S`, at the parameter `ϕ`; the same shape as `U1563.BurgessPhi`.  CITED KNOWN at `ϕ = 1/4` for
`S = CubeFree`; OPEN at any `ϕ < 1/3` for `S = NonCubeFree`. -/
def BurgessPhiOn (S : ℕ → Prop) (φ : ℝ) : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    S q → χ.IsPrimitive → χ ≠ 1 → ∀ s : ℂ, 1 - 1 / (k : ℝ) ≤ s.re → s.re ≤ 1 →
      ‖DirichletCharacter.LFunction χ s‖ ≤
        C * (q : ℝ) ^ (φ * (1 - s.re) * (1 + 1 / (k : ℝ)) + ε) * (1 + |s.im|)

/-- The all-moduli input of U-1563 restricts to any class. -/
theorem burgessPhiOn_of_all {S : ℕ → Prop} {φ : ℝ} (h : BurgessPhi φ) : BurgessPhiOn S φ := by
  intro k hk ε hε
  obtain ⟨C, hC⟩ := h k hk ε hε
  exact ⟨C, fun q _ χ _ hχ h1 s h1s h2s => hC q χ hχ h1 s h1s h2s⟩

/-- PROVED: the two halves give the all-moduli input, `C = max C₁ C₂`. -/
theorem burgessPhi_of_split {φ : ℝ} (hc : BurgessPhiOn CubeFree φ)
    (hn : BurgessPhiOn NonCubeFree φ) : BurgessPhi φ := by
  intro k hk ε hε
  obtain ⟨C₁, h₁⟩ := hc k hk ε hε
  obtain ⟨C₂, h₂⟩ := hn k hk ε hε
  refine ⟨max C₁ C₂, fun q _ χ hχ h1 s h1s h2s => ?_⟩
  have hp : 0 ≤ (q : ℝ) ^ (φ * (1 - s.re) * (1 + 1 / (k : ℝ)) + ε) := by positivity
  have ht : 0 ≤ 1 + |s.im| := by positivity
  by_cases hq : CubeFree q
  · calc _ ≤ C₁ * (q : ℝ) ^ (φ * (1 - s.re) * (1 + 1 / (k : ℝ)) + ε) * (1 + |s.im|) :=
          h₁ q χ hq hχ h1 s h1s h2s
      _ ≤ max C₁ C₂ * (q : ℝ) ^ (φ * (1 - s.re) * (1 + 1 / (k : ℝ)) + ε) * (1 + |s.im|) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hp) ht
  · calc _ ≤ C₂ * (q : ℝ) ^ (φ * (1 - s.re) * (1 + 1 / (k : ℝ)) + ε) * (1 + |s.im|) :=
          h₂ q χ hq hχ h1 s h1s h2s
      _ ≤ max C₁ C₂ * (q : ℝ) ^ (φ * (1 - s.re) * (1 + 1 / (k : ℝ)) + ε) * (1 + |s.im|) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hp) ht

/-- Vacuity: `BurgessPhiOn` holds at every `ϕ` on the class `{1}`, since mod 1 the only
character is principal. -/
theorem burgessPhiOn_one (φ : ℝ) : BurgessPhiOn (fun q => q = 1) φ := by
  intro k _ ε _
  refine ⟨0, fun q _ χ hq _ h1 => ?_⟩
  exact absurd (DirichletCharacter.level_one' χ hq) h1

/-- Vacuity for each named class Prop: on the empty class it holds at every `ϕ`. -/
theorem burgessPhiOn_empty (φ : ℝ) : BurgessPhiOn (fun _ => False) φ := by
  intro k _ ε _
  exact ⟨0, fun q _ χ hq => hq.elim⟩

/-! ## 3. The split method and its consequences -/

/-- CITED, a LAB GENERALISATION of U1563.ZhaoMethod, MODEL.  Plain twin: in Pintz's reduction
(2.26) to (2.33), a class with cube-free `q(R')` uses Lemma 2.5 only for characters mod a cube-free
`q`, so closes at weight `W` under `ϕ_c`; a class with non-cube-free `q(R')` closes at weight
`W_n ≥ W` under `ϕ_n`; a class with `q = X^θ` that cannot close costs `≪ X^{1-θ}` by (2.29).
Hence `E(X) ≪ X^{max(1-1/W, 1-1/W_n)+ε}`. -/
def SplitMethod (I : List (List ℝ) → Prop) : Prop :=
  ∀ φc φn W Wn : ℝ, 1 / 4 ≤ φc → φc ≤ 1 / 3 → 1 / 4 ≤ φn → φn ≤ 1 / 3 → 3 ≤ W → W ≤ Wn →
    BurgessPhiOn CubeFree φc → BurgessPhiOn NonCubeFree φn →
    Section4Closes φc W I → Section4Closes φn Wn I →
    ∀ ε : ℝ, 0 < ε → LeanLab.ExceptionalSet.PowerBound (max (1 - 1 / W) (1 - 1 / Wn) + ε)

/-- PROVED transfer: the split method contains U-1563's method as the diagonal case. -/
theorem zhaoMethod_of_split {I : List (List ℝ) → Prop} (h : SplitMethod I) : ZhaoMethod I := by
  intro φ W h1 h2 h3 hB hS ε hε
  have := h φ φ W W h1 h2 h1 h2 h3 le_rfl (burgessPhiOn_of_all hB) (burgessPhiOn_of_all hB)
    hS hS ε hε
  rwa [max_self] at this

/-- Vacuity for `SplitMethod`: it holds whenever the I-0133 target holds, since every exponent it
asserts is at least `2/3`.  So the Prop is consistent with the expected truth. -/
theorem splitMethod_of_target {I : List (List ℝ) → Prop} (hT : Target0133) : SplitMethod I := by
  intro φc φn W Wn _ _ _ _ hW _ _ _ _ _ ε hε
  apply LeanLab.ExceptionalSet.powerBound_mono _ (hT ε hε)
  have : (2 : ℝ) / 3 ≤ 1 - 1 / W := by
    have := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 3) hW
    linarith
  linarith [le_max_left (1 - 1 / W) (1 - 1 / Wn)]

/-- CONDITIONAL ON `SplitMethod I` CITED, `BurgessPhiOn CubeFree (1/4)` CITED KNOWN, Heath-Brown
1992 Lemma 2.5, `BurgessPhiOn NonCubeFree (1/4)` OPEN, and `Section4Closes (1/4) 3 I` OPEN and
TESTED: the exponent `2/3`.  The open Burgess input shrinks from all moduli to non-cube-free
moduli, but it does not disappear. -/
theorem target_of_split {I : List (List ℝ) → Prop} (hM : SplitMethod I)
    (hc : BurgessPhiOn CubeFree (1 / 4)) (hn : BurgessPhiOn NonCubeFree (1 / 4))
    (hS : Section4Closes (1 / 4) 3 I) : Target0133 := by
  intro ε hε
  have := hM (1 / 4) (1 / 4) 3 3 le_rfl (by norm_num) le_rfl (by norm_num) le_rfl le_rfl hc hn
    hS hS ε hε
  rwa [max_self, show (1 : ℝ) - 1 / 3 + ε = 2 / 3 + ε by ring] at this

/-- The NEGATIVE answer in Lean form: with only the KNOWN inputs, cube-free `ϕ = 1/4` and
all-moduli `ϕ = 1/3`, the non-cube-free classes need weight `10/3` and the split yields Zhao's
`7/10`, no matter how well the cube-free classes close.  CONDITIONAL ON `SplitMethod I` and on
Zhao's Section 4 at `(1/3, 10/3)`. -/
theorem split_gives_zhao {I : List (List ℝ) → Prop} (hM : SplitMethod I) {W : ℝ}
    (hW3 : 3 ≤ W) (hW : W ≤ 10 / 3)
    (hc : BurgessPhiOn CubeFree (1 / 4)) (hB : BurgessPhi (1 / 3))
    (hSc : Section4Closes (1 / 4) W I) (hSn : Section4Closes (1 / 3) (10 / 3) I) :
    ∀ ε : ℝ, 0 < ε → LeanLab.ExceptionalSet.PowerBound (7 / 10 + ε) := by
  intro ε hε
  have h := hM (1 / 4) (1 / 3) W (10 / 3) le_rfl (by norm_num) (by norm_num) le_rfl hW3 hW hc
    (burgessPhiOn_of_all hB) hSc hSn ε hε
  have hmax : max (1 - 1 / W) (1 - 1 / (10 / 3 : ℝ)) = 7 / 10 := by
    have : 1 - 1 / W ≤ 1 - 1 / (10 / 3 : ℝ) := by
      have := one_div_le_one_div_of_le (by linarith : (0:ℝ) < W) hW
      linarith
    rw [max_eq_right this]; norm_num
  rwa [hmax] at h

/-- The max in `SplitMethod` is attained by the worse half: improving only the cube-free weight
below the non-cube-free one never lowers the exponent. -/
theorem split_exponent_eq {W Wn : ℝ} (hW : 0 < W) (h : W ≤ Wn) :
    max (1 - 1 / W) (1 - 1 / Wn) = 1 - 1 / Wn := by
  apply max_eq_right
  have := one_div_le_one_div_of_le hW h
  linarith

/-- Exponent arithmetic: model floors `W*(1/4) = 2.991`, `W*(1/3) = 3.330`; the mixed exponent
is the non-cube-free one, `> 0.699`, against `2/3 < 0.6657 + 0.001`. -/
theorem mixed_exponents :
    max (1 - 1 / (2.991 : ℝ)) (1 - 1 / 3.330) = 1 - 1 / 3.330 ∧
      (0.699 : ℝ) < 1 - 1 / 3.330 ∧ (1 : ℝ) - 1 / 2.991 < 0.6657 := by
  refine ⟨split_exponent_eq (by norm_num) (by norm_num), by norm_num, by norm_num⟩

end LeanLab.Routes.U1585

end

#print axioms LeanLab.Routes.U1585.cubeFree_ne_zero
#print axioms LeanLab.Routes.U1585.cubeFree_of_dvd
#print axioms LeanLab.Routes.U1585.cubeFree_lcm
#print axioms LeanLab.Routes.U1585.cubeFree_foldr_lcm
#print axioms LeanLab.Routes.U1585.nonCubeFree_eight
#print axioms LeanLab.Routes.U1585.burgessPhiOn_of_all
#print axioms LeanLab.Routes.U1585.burgessPhi_of_split
#print axioms LeanLab.Routes.U1585.burgessPhiOn_one
#print axioms LeanLab.Routes.U1585.burgessPhiOn_empty
#print axioms LeanLab.Routes.U1585.zhaoMethod_of_split
#print axioms LeanLab.Routes.U1585.splitMethod_of_target
#print axioms LeanLab.Routes.U1585.target_of_split
#print axioms LeanLab.Routes.U1585.split_gives_zhao
#print axioms LeanLab.Routes.U1585.split_exponent_eq
#print axioms LeanLab.Routes.U1585.mixed_exponents
