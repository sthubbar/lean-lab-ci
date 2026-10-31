/-
P0085 Alsetri 2025, arXiv 2505.09648, Theorem 1.2 (`Alsetri12 m`, stated in Alsetri2025.lean)
for every odd squarefree m with 3 | m, 5 ∤ m and 7 ∤ m. Reduction: m = 3 m' with m' squarefree
and coprime to 210; by CRT a function supported on the classes ≡ 1 mod 3 is a function g on
Z_{m'}, Σ f = Σ g, φ(m) = 2 φ(m'), so Σ g > φ(m')/2 and Alsetri Prop 3.1 (`half31`,
AlsetriProp31.lean) gives the three summands mod m'; lift them with first coordinate 1 mod 3,
which sum to 0 mod 3.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
-/
import LeanLab.DensityGoldbach.AlsetriProp31
import LeanLab.DensityGoldbach.Alsetri2025

open Finset

namespace LeanLab.DensityGoldbach

/-- The first CRT coordinate of `z` mod `3 m'` is `z.val mod 3`. -/
lemma crt3_fst_val {m' : ℕ} [NeZero (3 * m')] (hc : Nat.Coprime 3 m') (z : ZMod (3 * m')) :
    ((ZMod.chineseRemainder hc z).1).val = z.val % 3 := by
  have h1 : ZMod.chineseRemainder hc z = ((z.val : ℕ) : ZMod 3 × ZMod m') := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    exact map_natCast (ZMod.chineseRemainder hc) z.val
  rw [h1, Prod.fst_natCast, ZMod.val_natCast]

lemma units3_eq : unitsMod 3 = {1, 2} := by decide

/-- **Reduction**: `Half31 m'` gives Theorem 1.2 at `3 m'`, for `m'` coprime to `3`. -/
theorem alsetri12_of_half31 (m' : ℕ) [NeZero m'] [NeZero (3 * m')] (hc : Nat.Coprime 3 m')
    (h : Half31 m') : Alsetri12 (3 * m') := by
  intro f hf hsupp hsum x hx
  set e := ZMod.chineseRemainder hc with he
  set g : ZMod m' → ℝ := fun y => f (e.symm (1, y)) with hg
  have hgbd : ∀ y, 0 ≤ g y ∧ g y ≤ 1 := fun y => hf _
  have h2 : ∀ v, f (e.symm (2, v)) = 0 := by
    intro v
    apply hsupp
    rw [← crt3_fst_val hc, RingEquiv.apply_symm_apply]
    show (2 : ZMod 3).val ≠ 1
    decide
  have hsum' : 1 / 2 * (m'.totient : ℝ) < ∑ a ∈ unitsMod m', g a := by
    rw [sum_unitsMod_crt hc, units3_eq, sum_pair (by decide), Nat.totient_mul hc,
      show Nat.totient 3 = 2 by decide] at hsum
    have h2' : ∑ v ∈ unitsMod m', f ((ZMod.chineseRemainder hc).symm (2, v)) = 0 :=
      sum_eq_zero fun v _ => h2 v
    rw [h2', add_zero] at hsum
    push_cast at hsum
    linarith
  obtain ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, hx2, hh⟩ := h g hgbd hsum' (e x).2
  have hx1 : (e x).1 = 0 := by
    have := crt3_fst_val hc x
    rw [hx] at this
    exact (ZMod.val_eq_zero _).1 this
  have hu1 : (1 : ZMod 3) ∈ unitsMod 3 := by decide
  have mem : ∀ a ∈ unitsMod m', e.symm (1, a) ∈ unitsMod (3 * m') := by
    intro a ha
    rw [mem_unitsMod_crt hc, RingEquiv.apply_symm_apply]
    exact ⟨hu1, ha⟩
  obtain ⟨p1, p2, p3, ps⟩ := hhalf_concl _ _ _ (hgbd a₁).1 (hgbd a₂).1 (hgbd a₃).1
    (hgbd a₁).2 (hgbd a₂).2 (hgbd a₃).2 hh
  refine ⟨e.symm (1, a₁), mem a₁ ha₁, e.symm (1, a₂), mem a₂ ha₂, e.symm (1, a₃), mem a₃ ha₃,
    ?_, p1, p2, p3, ps⟩
  apply e.injective
  rw [map_add, map_add, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
    RingEquiv.apply_symm_apply, Prod.mk_add_mk, Prod.mk_add_mk, ← hx2]
  ext
  · rw [hx1]; show (0 : ZMod 3) = 1 + 1 + 1; decide
  · rfl

/-- **P0085 Theorem 1.2** for `m` odd squarefree, `3 ∣ m`, `5 ∤ m`, `7 ∤ m`. -/
theorem alsetri12_of_coprime35 (m : ℕ) [NeZero m] (hodd : Odd m) (hsq : Squarefree m)
    (h3 : 3 ∣ m) (h5 : ¬ 5 ∣ m) (h7 : ¬ 7 ∣ m) : Alsetri12 m := by
  obtain ⟨m', rfl⟩ := h3
  have hm' : m' ≠ 0 := fun h => NeZero.ne (3 * m') (by simp [h])
  have : NeZero m' := ⟨hm'⟩
  have hsq' : Squarefree m' := hsq.of_mul_right
  have n3 : ¬ 3 ∣ m' := by
    rintro ⟨k, rfl⟩
    have := hsq 3 ⟨k, by ring⟩
    exact absurd (Nat.isUnit_iff.1 this) (by norm_num)
  have n2 : ¬ 2 ∣ m' := by
    rintro ⟨k, rfl⟩
    obtain ⟨r, hr⟩ := hodd
    omega
  have n5 : ¬ 5 ∣ m' := fun hd => h5 (Dvd.dvd.mul_left hd 3)
  have n7 : ¬ 7 ∣ m' := fun hd => h7 (Dvd.dvd.mul_left hd 3)
  have c2 : Nat.Coprime 2 m' := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 n2
  have c3 : Nat.Coprime 3 m' := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 n3
  have c5 : Nat.Coprime 5 m' := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 n5
  have c7 : Nat.Coprime 7 m' := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 n7
  have c210 : Nat.Coprime m' 210 := by
    have : Nat.Coprime (2 * 3 * 5 * 7) m' :=
      Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.Coprime.mul_left c2 c3) c5) c7
    exact this.symm
  exact alsetri12_of_half31 m' c3 (half31 m' hsq' c210)

end LeanLab.DensityGoldbach

#print axioms LeanLab.DensityGoldbach.alsetri12_of_coprime35
