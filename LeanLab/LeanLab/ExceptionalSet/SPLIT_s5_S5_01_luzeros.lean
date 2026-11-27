/-
Split of `Feed1122WindowCount.leaf_lu_major_and_mass39`, CLOUD S5 burst-20261127, unit S5-01.

P0095 W. C. Lu, Exceptional set of Goldbach number, J. Number Theory 130 (2010) 2359-2392.

The leaf asks for a family of exponents and a cutoff with the zero mass display (39), p. 2369,
and the major arc lower bound (84), p. 2391, or (85), p. 2392, for the expression (63), p. 2379.
The burst note of feed 1122 says the next step is a definition of Lu's zero family.  This file
gives it, `luFamily M N`: the nontrivial zeros `ρ`, `0 < Re ρ < 1`, `|Im ρ| ≤ M`, of `L(s, χ)`
for primitive `χ` of modulus `q ≤ P = N^c`, each repeated as often as its multiplicity, which is
the zero range of the sums in (36), (40), (41) and (63).  It also defines the case predicate
`SmallExc N` of p. 2391 and p. 2392: an exceptional zero `β̃ = 1 - λ̃ / log P` with
`λ̃ ≤ (log log log N)^-1`.

Leaves:
* `leaf_mass39_display`: display (39) itself, for the heights `T = 4πN/(qQ)`, `Q = N^(3/4)`.
* `leaf_major84_noexc`: display (84) for Lu's family, when `SmallExc N` fails.
* `leaf_major85_exc`: display (85) for Lu's family, when `SmallExc N` holds.

Proved here: `mass39_luFamily`, display (39) implies `Mass39 (luFamily M)` for every cutoff `M`,
because `M ≤ 4πN/(qQ)` for all `q ≤ P` once `N` is large; and the assembly
`leaf_lu_major_and_mass39_of_leaves`, the case split on `SmallExc N`.

Why not the empty family: `Feed1122WindowCount.leaf_of_major84` reduces the leaf to display (84)
WITHOUT the term `|D₆(k)|`.  That is not Lu's display.  `D₆` is exactly the source of the
exceptional set, via (86), and Lu only bounds it in mean square, not for each `k`.  A pointwise
(84) without `D₆` for every even `k` of the window, for all large `N`, would need control of the
zeros of characters of modulus between `P N^-0.0001` and `P` for every single `k`, and it also
fails to cover the Siegel zero case (85).  It is not a theorem of the paper and is not known
unconditionally; this file does not use that route.

AI wrote this Lean code.  Binary Goldbach is OPEN; this is the almost-all bound.
-/
import LeanLab.ExceptionalSet.Feed1122LeafWindowCount

namespace LeanLab.ExceptionalSet.SplitS5LuZeros
open LeanLab.ExceptionalSet
open LeanLab.ExceptionalSet.Lu2010Assembly
open LeanLab.ExceptionalSet.Lu2010Formula63
open LeanLab.ExceptionalSet.Lu2010Main63
open LeanLab.ExceptionalSet.Lu2010ZeroIntegral

attribute [local instance] Classical.propDecidable

/-- Lu 2010, p. 2368, the zeros summed in `W₀(q, T, x) = Σ*_{χ mod q} Σ_{|γ| ≤ T} x^(β-1)` and in
(41) and (63): exponents whose modulus is at most `P = N^c`, whose `ρ` is a nontrivial zero of
`L(s, χ)`, `0 < Re ρ < 1`, with `|Im ρ| ≤ H q`, and whose label is below the multiplicity of the
zero, so that each zero is counted with multiplicity.  The analytic order is `0` where `L` does
not vanish. -/
def luZeroSet (H : ℕ → ℝ) (N : ℕ) : Set Exponent :=
  {x | (x.modulus : ℝ) ≤ PP N ∧ 0 < x.rho.re ∧ x.rho.re < 1 ∧ |x.rho.im| ≤ H x.modulus ∧
    ((x.label : ℕ∞) < analyticOrderAt (DirichletCharacter.LFunction x.character) x.rho)}

/-- The zero set of `luZeroSet` as a `Finset`.  It is finite: finitely many primitive characters
of modulus at most `P`, finitely many zeros of each `L(s, χ)` in a bounded box, each of finite
multiplicity.  The lab has not proved that finiteness, so the definition falls back to `∅`
otherwise; display (39), `leaf_mass39_display`, asserts the finiteness it needs. -/
noncomputable def luFamilyH (H : ℕ → ℕ → ℝ) (N : ℕ) : Finset Exponent :=
  if h : (luZeroSet (H N) N).Finite then h.toFinset else ∅

/-- Lu's zero family with the constant height cutoff `M` of (40), (41), (63). -/
noncomputable def luFamily (M : ℝ) : ℕ → Finset Exponent := luFamilyH (fun _ _ => M)

/-- The heights of display (39): `T = 4πN/(qQ)` with `Q = N^(3/4)`, Lu 2010 p. 2363. -/
noncomputable def height39 (N q : ℕ) : ℝ :=
  4 * Real.pi * N / (q * (N : ℝ) ^ (3 / 4 : ℝ))

/-- The case predicate of Lu 2010, pp. 2391-2392: an exceptional zero `β̃ = 1 - λ̃ / log P` with
`λ̃ ≤ (log log log N)^-1`, written as a real zero `0 < β < 1` of `L(s, χ)` for a primitive `χ` of
modulus at most `P`.  For large `N` any such zero is the exceptional zero of Page's theorem,
because `λ̃ → 0` places it inside the classical zero free region. -/
def SmallExc (N : ℕ) : Prop :=
  ∃ x : Exponent, (x.modulus : ℝ) ≤ PP N ∧ x.rho.im = 0 ∧ 0 < x.rho.re ∧ x.rho.re < 1 ∧
    DirichletCharacter.LFunction x.character x.rho = 0 ∧
    (1 - x.rho.re) * Real.log (PP N) ≤ (Real.log (Real.log (Real.log N)))⁻¹

/-- LEAF: Lu 2010, p. 2369 display (39), `Σ_{q ≤ P} W₀(q, 4πN/(qQ), N) ≪ 1`. HARD.
From the zero density estimates (37) and (38) of Huxley and Jutila by the usual method.
Stated with the finiteness of the zero set, which is true and which the sum needs. -/
theorem leaf_mass39_display :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (luZeroSet (height39 N) N).Finite ∧
      ∑ x ∈ luFamilyH height39 N, weight N x.rho ≤ C := by
  sorry

/-- LEAF: Lu 2010, p. 2391 display (84), the case without an exceptional zero or with
`λ̃ > (log log log N)^-1`. HARD.
For every large cutoff `M`, the major arc integral exceeds
`S(k)(b-a)d((log log log N)^-1 + O((log log N)^-1/2)) - |D₆(k)|` on the window, with `D₆` the
printed expression (63) for Lu's zero family.  Lu derives it from (27), (29), (83) and the
bounds for `D₄` of Section 10.  The `O` constant may be enlarged, hence the `∀ Cerr ≥ Cerr0`. -/
theorem leaf_major84_noexc :
    ∃ M0 : ℝ, ∀ M : ℝ, M0 ≤ M → ∃ Cerr0 : ℝ, ∀ Cerr : ℝ, Cerr0 ≤ Cerr → ∃ N0 : ℕ,
      ∀ N : ℕ, N0 ≤ N → ¬ SmallExc N → ∀ k ∈ Win N, Even k →
        LeanLab.ExceptionalSet.BG2026.Sing k * (bb N - aa N) * dd N *
          ((Real.log (Real.log (Real.log N)))⁻¹ - Cerr * (Real.log (Real.log N)) ^ (-(1 / 2) : ℝ))
          - ‖Lu2010Eq63.printed63 N (luFamily M N) M k‖ < (Lu2010Arcs.D1c N k).re := by
  sorry

/-- LEAF: Lu 2010, p. 2392 display (85), the case `λ̃ ≤ (log log log N)^-1`. HARD.
For every large cutoff `M` there is `c₁ > 0`, from Siegel's theorem, with
`D₁(k) ≥ S(k)(b-a)d c₁ P^-0.00001 log P (2c^-1 + O((log log log N)^-0.1)) - |D₆(k)|` on the
window.  Lu derives it from Lemma 35, (64), (27), (29), Jutila's density estimate and (38). -/
theorem leaf_major85_exc :
    ∃ M0 : ℝ, ∀ M : ℝ, M0 ≤ M → ∃ c1 : ℝ, 0 < c1 ∧ ∃ Cerr0 : ℝ, ∀ Cerr : ℝ, Cerr0 ≤ Cerr →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → SmallExc N → ∀ k ∈ Win N, Even k →
        LeanLab.ExceptionalSet.BG2026.Sing k * (bb N - aa N) * dd N * c1 * PP N ^ (-0.00001 : ℝ) *
          Real.log (PP N) * (2 * c⁻¹ - Cerr * (Real.log (Real.log (Real.log N))) ^ (-0.1 : ℝ))
          - ‖Lu2010Eq63.printed63 N (luFamily M N) M k‖ ≤ (Lu2010Arcs.D1c N k).re := by
  sorry

/-- For `1 ≤ q ≤ P` and `N ≥ 1`, `N^0.1285 ≤ 4πN/(qQ)`. -/
theorem rpow_le_height39 {N q : ℕ} (hN : 1 ≤ N) (hq : 1 ≤ q) (hqP : (q : ℝ) ≤ PP N) :
    (N : ℝ) ^ (0.1285 : ℝ) ≤ height39 N q := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  unfold height39
  have hpos : 0 < (q : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) := by positivity
  rw [le_div_iff₀ hpos]
  have h1 : (q : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) ≤ (N : ℝ) ^ c * (N : ℝ) ^ (3 / 4 : ℝ) :=
    mul_le_mul_of_nonneg_right hqP (by positivity)
  have h2 : (N : ℝ) ^ (0.1285 : ℝ) * ((N : ℝ) ^ c * (N : ℝ) ^ (3 / 4 : ℝ)) = N := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
    unfold c
    norm_num
  have h3 : (N : ℝ) ≤ 4 * Real.pi * N := by
    have : (1 : ℝ) ≤ 4 * Real.pi := by linarith [Real.pi_gt_three]
    nlinarith
  calc (N : ℝ) ^ (0.1285 : ℝ) * ((q : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ))
      ≤ (N : ℝ) ^ (0.1285 : ℝ) * ((N : ℝ) ^ c * (N : ℝ) ^ (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = N := h2
    _ ≤ 4 * Real.pi * N := h3

/-- Display (39) gives `Mass39` for Lu's family with any constant cutoff `M`: for large `N` the
cutoff is below every height `4πN/(qQ)`, `q ≤ P`, and the weights `N^(β-1)` are nonnegative. -/
theorem mass39_luFamily (h39 : ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      (luZeroSet (height39 N) N).Finite ∧
      ∑ x ∈ luFamilyH height39 N, weight N x.rho ≤ C) (M : ℝ) :
    Mass39 (luFamily M) := by
  obtain ⟨C, hC0, N0, h⟩ := h39
  have hev : ∀ᶠ N : ℕ in Filter.atTop, M ≤ (N : ℝ) ^ (0.1285 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.1285)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop M
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hev
  refine ⟨C, hC0, max N0 N1, fun N hN hN1' => ?_⟩
  obtain ⟨hfin, hsum⟩ := h N (le_trans (le_max_left _ _) hN)
  have hM := hN1 N (le_trans (le_max_right _ _) hN)
  have hsub : luZeroSet (fun _ => M) N ⊆ luZeroSet (height39 N) N := by
    rintro x ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, h3, ?_, h5⟩
    have hq : 1 ≤ x.modulus := x.modulus_pos
    exact le_trans h4 (le_trans hM (rpow_le_height39 hN1' hq h1))
  have hfin' : (luZeroSet (fun _ => M) N).Finite := hfin.subset hsub
  have hfam : luFamily M N = hfin'.toFinset := by
    unfold luFamily luFamilyH
    simp only [dif_pos hfin']
  have hbig : luFamilyH height39 N = hfin.toFinset := by
    unfold luFamilyH
    simp only [dif_pos hfin]
  rw [hbig] at hsum
  rw [hfam]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hsum
  · intro x hx
    rw [Set.Finite.mem_toFinset] at hx ⊢
    exact hsub hx
  · intro x _ _
    unfold weight
    positivity

/-- `leaf_lu_major_and_mass39` of `Feed1122WindowCount`, statement verbatim, from the leaves:
Lu's zero family with a cutoff large for both displays, and the case split on `SmallExc N`. -/
theorem leaf_lu_major_and_mass39_of_leaves :
    ∃ (family : ℕ → Finset Exponent) (M : ℕ → ℝ),
      Mass39 family ∧ Nonempty (MajorInputs63 family M) := by
  obtain ⟨MB, hB⟩ := leaf_major84_noexc
  obtain ⟨MC, hC⟩ := leaf_major85_exc
  obtain ⟨CB, hB'⟩ := hB (max MB MC) (le_max_left _ _)
  obtain ⟨c1, hc1, CC, hC'⟩ := hC (max MB MC) (le_max_right _ _)
  obtain ⟨NB, hNB⟩ := hB' (max CB CC) (le_max_left _ _)
  obtain ⟨NC, hNC⟩ := hC' (max CB CC) (le_max_right _ _)
  refine ⟨luFamily (max MB MC), fun _ => max MB MC,
    mass39_luFamily leaf_mass39_display (max MB MC),
    ⟨⟨max NB NC, max CB CC, c1, hc1, fun N hN => ?_⟩⟩⟩
  by_cases h : SmallExc N
  · exact Or.inr (hNC N (le_trans (le_max_right _ _) hN) h)
  · exact Or.inl (hNB N (le_trans (le_max_left _ _) hN) h)

example : type_of% @LeanLab.ExceptionalSet.Feed1122WindowCount.leaf_lu_major_and_mass39 :=
  leaf_lu_major_and_mass39_of_leaves

end LeanLab.ExceptionalSet.SplitS5LuZeros

#print axioms LeanLab.ExceptionalSet.SplitS5LuZeros.rpow_le_height39
#print axioms LeanLab.ExceptionalSet.SplitS5LuZeros.mass39_luFamily
#print axioms LeanLab.ExceptionalSet.SplitS5LuZeros.leaf_lu_major_and_mass39_of_leaves
