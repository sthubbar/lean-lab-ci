/-
P0087 Akeno 2026 Appendix 5.1 page 36.
Grid 1/160 certificates. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.SieveCTables160Data
namespace LeanLab.Akeno2026.SieveFns.Grid160
theorem chk_c4_1120 : ∀ k < 1200, 1120 ≤ k → checks4 k := by
  unfold checks4
  decide +kernel
end LeanLab.Akeno2026.SieveFns.Grid160
