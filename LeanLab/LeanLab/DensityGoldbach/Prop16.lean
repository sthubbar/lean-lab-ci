/-
P0038 Shao 2012, Proposition 1.6, the local result behind Theorem 1.3: m odd squarefree with
3 ∣ m, f on the reduced residues mod m, αᵢ the average of f over the reduced residues ≡ i mod 3;
if 2α₁ + α₂ > 3/2 and 2α₂ + α₁ > 3/2 then every x mod m is a₁ + a₂ + a₃, reduced, with
f a₁ + f a₂ + f a₃ > 3/2. As in the paper: CRT m = 3 m', a choice of residues mod 3, then
Li-Pan Theorem 1.2 mod m'. The paper assumes f takes values in (0, 1]; the proof never uses
it, so the Lean statement has no range hypothesis and is formally stronger.
AI-written Lean code, Claude, 2026-10-17, run 20261017T0102Z-30056, unit U-0127.
-/
import LeanLab.DensityGoldbach.LiPanLocal

open Finset

namespace LeanLab.DensityGoldbach

/-- The average of `f` over the reduced residues `r` mod `m` with `r ≡ i mod 3`. -/
noncomputable def alphaRes (m : ℕ) [NeZero m] (f : ZMod m → ℝ) (i : ZMod 3) : ℝ :=
  (∑ r ∈ (unitsMod m).filter (fun r => ((r.val : ℕ) : ZMod 3) = i), f r) /
    #((unitsMod m).filter (fun r => ((r.val : ℕ) : ZMod 3) = i))

lemma crt_fst_eq {k : ℕ} [NeZero k] (hk : Nat.Coprime 3 k) (r : ZMod (3 * k)) :
    (ZMod.chineseRemainder hk r).1 = ((r.val : ℕ) : ZMod 3) := by
  have h : (RingHom.fst (ZMod 3) (ZMod k)).comp (ZMod.chineseRemainder hk).toRingHom =
      ZMod.castHom (dvd_mul_right 3 k) (ZMod 3) := RingHom.ext_zmod _ _
  have := congrArg (fun φ => φ r) h
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, ZMod.castHom_apply] at this
  exact this.trans (ZMod.cast_eq_val r)

/-- The fiber of the reduced residues over a unit `i` mod 3. -/
lemma sum_fiber3 {k : ℕ} [NeZero k] [NeZero (3 * k)] (hk : Nat.Coprime 3 k) (f : ZMod (3 * k) → ℝ)
    (i : ZMod 3) (hi : i ≠ 0) :
    ∑ r ∈ (unitsMod (3 * k)).filter (fun r => ((r.val : ℕ) : ZMod 3) = i), f r =
      ∑ u ∈ unitsMod k, f ((ZMod.chineseRemainder hk).symm (i, u)) := by
  have : NeZero 3 := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set e := ZMod.chineseRemainder hk
  refine sum_nbij' (fun r => (e r).2) (fun u => e.symm (i, u)) ?_ ?_ ?_ ?_ ?_
  · intro r hr
    rw [mem_filter] at hr
    exact ((mem_unitsMod_crt hk r).1 hr.1).2
  · intro u hu
    rw [mem_filter, mem_unitsMod_crt hk, RingEquiv.apply_symm_apply, ← crt_fst_eq hk,
      RingEquiv.apply_symm_apply]
    exact ⟨⟨(mem_unitsMod _).2 (isUnit_iff_ne_zero.2 hi), hu⟩, rfl⟩
  · intro r hr
    rw [mem_filter, ← crt_fst_eq hk] at hr
    apply e.injective
    rw [RingEquiv.apply_symm_apply, ← hr.2]
  · intro u _; simp
  · intro r hr
    rw [mem_filter, ← crt_fst_eq hk] at hr
    congr 1
    apply e.injective
    rw [RingEquiv.apply_symm_apply, ← hr.2]

lemma alphaRes_eq {k : ℕ} [NeZero k] [NeZero (3 * k)] (hk : Nat.Coprime 3 k)
    (f : ZMod (3 * k) → ℝ) (i : ZMod 3) (hi : i ≠ 0) :
    alphaRes (3 * k) f i =
      (∑ u ∈ unitsMod k, f ((ZMod.chineseRemainder hk).symm (i, u))) / k.totient := by
  rw [alphaRes, sum_fiber3 hk f i hi]
  congr 1
  have h1 := sum_fiber3 hk (fun _ => (1 : ℝ)) i hi
  simp only [sum_const, nsmul_one] at h1
  rw [h1]
  have : #(unitsMod k) = k.totient := by
    rw [unitsMod, ← ZMod.card_units_eq_totient, ← Fintype.card_coe]
    exact Fintype.card_congr
      { toFun := fun u => IsUnit.unit (mem_filter.1 u.2).2
        invFun := fun u => ⟨(u : ZMod k), mem_filter.2 ⟨mem_univ _, u.isUnit⟩⟩
        left_inv := fun u => by simp
        right_inv := fun u => by ext; simp }
  rw [this]

/-- The finishing step for one choice of residues `i₁, i₂, i₃` mod 3. -/
lemma prop16_finish {k : ℕ} [NeZero k] [NeZero (3 * k)] (hk : Nat.Coprime 3 k)
    (hLP : LiPan12 k) (f : ZMod (3 * k) → ℝ) (x : ZMod (3 * k)) (i₁ i₂ i₃ : ZMod 3)
    (h₁ : i₁ ≠ 0) (h₂ : i₂ ≠ 0) (h₃ : i₃ ≠ 0)
    (hx : i₁ + i₂ + i₃ = (ZMod.chineseRemainder hk x).1)
    (hα : 3 / 2 < alphaRes (3 * k) f i₁ + alphaRes (3 * k) f i₂ + alphaRes (3 * k) f i₃) :
    ∃ a₁ ∈ unitsMod (3 * k), ∃ a₂ ∈ unitsMod (3 * k), ∃ a₃ ∈ unitsMod (3 * k),
      x = a₁ + a₂ + a₃ ∧ 3 / 2 < f a₁ + f a₂ + f a₃ := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set e := ZMod.chineseRemainder hk
  rw [alphaRes_eq hk f i₁ h₁, alphaRes_eq hk f i₂ h₂, alphaRes_eq hk f i₃ h₃] at hα
  obtain ⟨u₁, hu₁, u₂, hu₂, u₃, hu₃, hn, hK⟩ := hLP (fun u => f (e.symm (i₁, u)))
    (fun u => f (e.symm (i₂, u))) (fun u => f (e.symm (i₃, u))) (e x).2
  have hunit : ∀ i : ZMod 3, i ≠ 0 → ∀ u ∈ unitsMod k, e.symm (i, u) ∈ unitsMod (3 * k) := by
    intro i hi u hu
    rw [mem_unitsMod_crt hk, RingEquiv.apply_symm_apply]
    exact ⟨(mem_unitsMod _).2 (isUnit_iff_ne_zero.2 hi), hu⟩
  refine ⟨e.symm (i₁, u₁), hunit i₁ h₁ u₁ hu₁, e.symm (i₂, u₂), hunit i₂ h₂ u₂ hu₂,
    e.symm (i₃, u₃), hunit i₃ h₃ u₃ hu₃, ?_, ?_⟩
  · apply e.injective
    rw [map_add, map_add, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply, Prod.mk_add_mk, Prod.mk_add_mk, hx, hn]
  · refine lt_of_lt_of_le ?_ hK
    rw [add_div, add_div]
    exact hα

/-- **Shao Proposition 1.6.** -/
theorem shao_prop16 (m : ℕ) [NeZero m] (hodd : Odd m) (hsq : Squarefree m) (h3 : 3 ∣ m)
    (f : ZMod m → ℝ)
    (hα₁ : 3 / 2 < 2 * alphaRes m f 1 + alphaRes m f 2)
    (hα₂ : 3 / 2 < 2 * alphaRes m f 2 + alphaRes m f 1) (x : ZMod m) :
    ∃ a₁ ∈ unitsMod m, ∃ a₂ ∈ unitsMod m, ∃ a₃ ∈ unitsMod m,
      x = a₁ + a₂ + a₃ ∧ 3 / 2 < f a₁ + f a₂ + f a₃ := by
  obtain ⟨k, rfl⟩ := h3
  have hk0 : k ≠ 0 := by rintro rfl; exact NeZero.ne (3 * 0) rfl
  have : NeZero k := ⟨hk0⟩
  have hk3 : Nat.Coprime 3 k := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h
    exact Nat.prime_three.one_lt.ne' (Nat.isUnit_iff.1 (hsq 3 (mul_dvd_mul_left 3 h)))
  have hk6 : k.Coprime 6 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.coprime_mul_iff_right]
    refine ⟨?_, hk3.symm⟩
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro h
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (dvd_mul_of_dvd_right h 3))
  have hLP := liPan12_squarefree k (hsq.squarefree_of_dvd (dvd_mul_left k 3)) hk6
  set i := (ZMod.chineseRemainder hk3 x).1 with hi
  have one_ne : (1 : ZMod 3) ≠ 0 := by decide
  have two_ne : (2 : ZMod 3) ≠ 0 := by decide
  have key : ∀ j : ZMod 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  rcases key i with h | h | h
  · by_cases hα : 1 / 2 < alphaRes (3 * k) f 1
    · exact prop16_finish hk3 hLP f x 1 1 1 one_ne one_ne one_ne
        (by rw [← hi, h]; decide) (by linarith)
    · exact prop16_finish hk3 hLP f x 2 2 2 two_ne two_ne two_ne
        (by rw [← hi, h]; decide) (by linarith)
  · exact prop16_finish hk3 hLP f x 1 1 2 one_ne one_ne two_ne
      (by rw [← hi, h]; decide) (by linarith)
  · exact prop16_finish hk3 hLP f x 1 2 2 one_ne two_ne two_ne
      (by rw [← hi, h]; decide) (by linarith)

end LeanLab.DensityGoldbach

#print axioms LeanLab.DensityGoldbach.shao_prop16
