/-
Prove2Me mission 6d14203d, dependency PrimorialCertData_64.
Author bwdaugherty. Apache 2.0.
https://prove2.me/theorems/86b86403-d63f-41e8-9e32-102264af4083
Certificate data for LL_Decomp551a.primorial_c5_lower_first and the other three c5 leaves.
Derived certificate for Schoenfeld 1976 page 356 display 5.1 star.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.LiuWang2002.P2M655Core

set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace LeanLab.LiuWang2002.P2M655

namespace ThetaSieve
def PrimData64.s0 : Seg := ⟨535750101994031776849775186, 535750101994031787009414183, 29048835, 4096, [], 535894654217488910972109512, 535894654217488921134489834⟩
def PrimData64.s1 : Seg := ⟨535894654217488910972109512, 535894654217488921134489834, 29057027, 4096, [], 536043329884513818370796922, 536043329884513828535995882⟩
def PrimData64.s2 : Seg := ⟨536043329884513818370796922, 536043329884513828535995882, 29065219, 4096, [], 536193593046932409694469317, 536193593046932419862516717⟩
def PrimData64.s3 : Seg := ⟨536193593046932409694469317, 536193593046932419862516717, 29073411, 4096, [], 536346394803185768667842034, 536346394803185778838786856⟩
def PrimData64.s4 : Seg := ⟨536346394803185768667842034, 536346394803185778838786856, 29081603, 4096, [], 536497613950525275328735823, 536497613950525285502547454⟩
def PrimData64.s5 : Seg := ⟨536497613950525275328735823, 536497613950525285502547454, 29089795, 4096, [], 536647250436161714315156387, 536647250436161724491805101⟩
def PrimData64.s6 : Seg := ⟨536647250436161714315156387, 536647250436161724491805101, 29097987, 4096, [], 536798474531885365216499609, 536798474531885375396015225⟩
def PrimData64.s7 : Seg := ⟨536798474531885365216499609, 536798474531885375396015225, 29106179, 4096, [], 536951920371993506637745448, 536951920371993516820171110⟩
def PrimData64.s8 : Seg := ⟨536951920371993506637745448, 536951920371993516820171110, 29114371, 4096, [], 537100930122815731954244062, 537100930122815742139494949⟩
def PrimData64.s9 : Seg := ⟨537100930122815731954244062, 537100930122815742139494949, 29122563, 4096, [], 537254698033073346982877677, 537254698033073357171044295⟩
def PrimData64.s10 : Seg := ⟨537254698033073346982877677, 537254698033073357171044295, 29130755, 4096, [], 537400859203257209176211918, 537400859203257219367149936⟩
def PrimData64.s11 : Seg := ⟨537400859203257209176211918, 537400859203257219367149936, 29138947, 4096, [], 537549242154479065146903156, 537549242154479075340654212⟩
def PrimData64.s12 : Seg := ⟨537549242154479065146903156, 537549242154479075340654212, 29147139, 4096, [], 537701115201173420858738196, 537701115201173431055368811⟩
def PrimData64.s13 : Seg := ⟨537701115201173420858738196, 537701115201173431055368811, 29155331, 4096, [], 537850137116479996077490416, 537850137116480006276947173⟩
def PrimData64.s14 : Seg := ⟨537850137116479996077490416, 537850137116480006276947173, 29163523, 4096, [], 537997259079970665373845656, 537997259079970675576092743⟩
def PrimData64.s15 : Seg := ⟨537997259079970665373845656, 537997259079970675576092743, 29171715, 4096, [], 538151042071459778966262120, 538151042071459789171426526⟩
def PrimData64.s16 : Seg := ⟨538151042071459778966262120, 538151042071459789171426526, 29179907, 4096, [], 538298485910115970671183706, 538298485910115980879144792⟩
def PrimData64.s17 : Seg := ⟨538298485910115970671183706, 538298485910115980879144792, 29188099, 4096, [], 538456396132947329009010599, 538456396132947339219966854⟩
def PrimData64.s18 : Seg := ⟨538456396132947329009010599, 538456396132947339219966854, 29196291, 4096, [], 538602576385257625789511100, 538602576385257636003240020⟩
def PrimData64.s19 : Seg := ⟨538602576385257625789511100, 538602576385257636003240020, 29204483, 4096, [], 538760491726024962784189833, 538760491726024973000914291⟩
def PrimData64.s20 : Seg := ⟨538760491726024962784189833, 538760491726024973000914291, 29212675, 4096, [], 538906359656286496959946278, 538906359656286507179437893⟩
def PrimData64.s21 : Seg := ⟨538906359656286496959946278, 538906359656286507179437893, 29220867, 4096, [], 539056669564032493702488200, 539056669564032503924830321⟩
def PrimData64.s22 : Seg := ⟨539056669564032493702488200, 539056669564032503924830321, 29229059, 4096, [], 539195565763382437269256060, 539195565763382447494232417⟩
def PrimData64.s23 : Seg := ⟨539195565763382437269256060, 539195565763382447494232417, 29237251, 4096, [], 539344929148127885066816426, 539344929148127895294626522⟩
def PrimData64.s24 : Seg := ⟨539344929148127885066816426, 539344929148127895294626522, 29245443, 4096, [], 539496514871481710317141349, 539496514871481720547827466⟩
def PrimData64.s25 : Seg := ⟨539496514871481710317141349, 539496514871481720547827466, 29253635, 4096, [], 539650322919824314840485118, 539650322919824325074088809⟩
def PrimData64.s26 : Seg := ⟨539650322919824314840485118, 539650322919824325074088809, 29261827, 4096, [], 539804767760243876821152529, 539804767760243887057684972⟩
def PrimData64.s27 : Seg := ⟨539804767760243876821152529, 539804767760243887057684972, 29270019, 4096, [], 539956043714130191072197133, 539956043714130201311599279⟩
def PrimData64.s28 : Seg := ⟨539956043714130191072197133, 539956043714130201311599279, 29278211, 4096, [], 540107322150534593982792632, 540107322150534604225063510⟩
def PrimData64.s29 : Seg := ⟨540107322150534593982792632, 540107322150534604225063510, 29286403, 4096, [], 540266848891661084875995628, 540266848891661095121292461⟩
def PrimData64.s30 : Seg := ⟨540266848891661084875995628, 540266848891661095121292461, 29294595, 4096, [], 540422255226161074338325548, 540422255226161084586570091⟩
def PrimData64.s31 : Seg := ⟨540422255226161074338325548, 540422255226161084586570091, 29302787, 4096, [], 540577664111465730607204509, 540577664111465740858396517⟩
def PrimData64.s32 : Seg := ⟨540577664111465730607204509, 540577664111465740858396517, 29310979, 4096, [], 540725146406614500982590209, 540725146406614511236579023⟩
def PrimData64.s33 : Seg := ⟨540725146406614500982590209, 540725146406614511236579023, 29319171, 4096, [], 540877705778520270998011564, 540877705778520281254894385⟩
def PrimData64.s34 : Seg := ⟨540877705778520270998011564, 540877705778520281254894385, 29327363, 4096, [], 541035659697993160850536466, 541035659697993171110415113⟩

def PrimData64.segs : List Seg := [PrimData64.s0, PrimData64.s1, PrimData64.s2, PrimData64.s3, PrimData64.s4, PrimData64.s5, PrimData64.s6, PrimData64.s7, PrimData64.s8, PrimData64.s9, PrimData64.s10, PrimData64.s11, PrimData64.s12, PrimData64.s13, PrimData64.s14, PrimData64.s15, PrimData64.s16, PrimData64.s17, PrimData64.s18, PrimData64.s19, PrimData64.s20, PrimData64.s21, PrimData64.s22, PrimData64.s23, PrimData64.s24, PrimData64.s25, PrimData64.s26, PrimData64.s27, PrimData64.s28, PrimData64.s29, PrimData64.s30, PrimData64.s31, PrimData64.s32, PrimData64.s33, PrimData64.s34]

end ThetaSieve


namespace ThetaSieve
theorem checked64_s0 : Seg.bok PrimData64.s0 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s0

theorem checked64_s1 : Seg.bok PrimData64.s1 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s1

theorem checked64_s2 : Seg.bok PrimData64.s2 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s2

theorem checked64_s3 : Seg.bok PrimData64.s3 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s3

theorem checked64_s4 : Seg.bok PrimData64.s4 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s4

theorem checked64_s5 : Seg.bok PrimData64.s5 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s5

theorem checked64_s6 : Seg.bok PrimData64.s6 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s6

theorem checked64_s7 : Seg.bok PrimData64.s7 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s7

theorem checked64_s8 : Seg.bok PrimData64.s8 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s8

theorem checked64_s9 : Seg.bok PrimData64.s9 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s9

theorem checked64_s10 : Seg.bok PrimData64.s10 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s10

theorem checked64_s11 : Seg.bok PrimData64.s11 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s11

theorem checked64_s12 : Seg.bok PrimData64.s12 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s12

theorem checked64_s13 : Seg.bok PrimData64.s13 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s13

theorem checked64_s14 : Seg.bok PrimData64.s14 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s14

theorem checked64_s15 : Seg.bok PrimData64.s15 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s15

theorem checked64_s16 : Seg.bok PrimData64.s16 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s16

theorem checked64_s17 : Seg.bok PrimData64.s17 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s17

theorem checked64_s18 : Seg.bok PrimData64.s18 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s18

theorem checked64_s19 : Seg.bok PrimData64.s19 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s19

theorem checked64_s20 : Seg.bok PrimData64.s20 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s20

theorem checked64_s21 : Seg.bok PrimData64.s21 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s21

theorem checked64_s22 : Seg.bok PrimData64.s22 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s22

theorem checked64_s23 : Seg.bok PrimData64.s23 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s23

theorem checked64_s24 : Seg.bok PrimData64.s24 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s24

theorem checked64_s25 : Seg.bok PrimData64.s25 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s25

theorem checked64_s26 : Seg.bok PrimData64.s26 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s26

theorem checked64_s27 : Seg.bok PrimData64.s27 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s27

theorem checked64_s28 : Seg.bok PrimData64.s28 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s28

theorem checked64_s29 : Seg.bok PrimData64.s29 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s29

theorem checked64_s30 : Seg.bok PrimData64.s30 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s30

theorem checked64_s31 : Seg.bok PrimData64.s31 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s31

theorem checked64_s32 : Seg.bok PrimData64.s32 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s32

theorem checked64_s33 : Seg.bok PrimData64.s33 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s33

theorem checked64_s34 : Seg.bok PrimData64.s34 = true := by
  decide +kernel
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64_s34

 theorem checked64 : ∀ s ∈ PrimData64.segs, (Seg.bok s) = true := by
  unfold PrimData64.segs
  exact List.forall_mem_cons.2 ⟨checked64_s0, List.forall_mem_cons.2 ⟨checked64_s1, List.forall_mem_cons.2 ⟨checked64_s2, List.forall_mem_cons.2 ⟨checked64_s3, List.forall_mem_cons.2 ⟨checked64_s4, List.forall_mem_cons.2 ⟨checked64_s5, List.forall_mem_cons.2 ⟨checked64_s6, List.forall_mem_cons.2 ⟨checked64_s7, List.forall_mem_cons.2 ⟨checked64_s8, List.forall_mem_cons.2 ⟨checked64_s9, List.forall_mem_cons.2 ⟨checked64_s10, List.forall_mem_cons.2 ⟨checked64_s11, List.forall_mem_cons.2 ⟨checked64_s12, List.forall_mem_cons.2 ⟨checked64_s13, List.forall_mem_cons.2 ⟨checked64_s14, List.forall_mem_cons.2 ⟨checked64_s15, List.forall_mem_cons.2 ⟨checked64_s16, List.forall_mem_cons.2 ⟨checked64_s17, List.forall_mem_cons.2 ⟨checked64_s18, List.forall_mem_cons.2 ⟨checked64_s19, List.forall_mem_cons.2 ⟨checked64_s20, List.forall_mem_cons.2 ⟨checked64_s21, List.forall_mem_cons.2 ⟨checked64_s22, List.forall_mem_cons.2 ⟨checked64_s23, List.forall_mem_cons.2 ⟨checked64_s24, List.forall_mem_cons.2 ⟨checked64_s25, List.forall_mem_cons.2 ⟨checked64_s26, List.forall_mem_cons.2 ⟨checked64_s27, List.forall_mem_cons.2 ⟨checked64_s28, List.forall_mem_cons.2 ⟨checked64_s29, List.forall_mem_cons.2 ⟨checked64_s30, List.forall_mem_cons.2 ⟨checked64_s31, List.forall_mem_cons.2 ⟨checked64_s32, List.forall_mem_cons.2 ⟨checked64_s33, List.forall_mem_singleton.2 checked64_s34⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end ThetaSieve
end LeanLab.LiuWang2002.P2M655
#print axioms LeanLab.LiuWang2002.P2M655.ThetaSieve.checked64
