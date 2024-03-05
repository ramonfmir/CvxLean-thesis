import CvxLean

noncomputable section

open CvxLean Minimization Real

namespace Chapter4

namespace SqrtAtom

/-! Section 4.2.4 and 4.5 -/

-- <https://github.com/verified-optimization/CvxLean/blob/main/CvxLean/Tactic/DCP/AtomLibrary/Fns/Sqrt.lean>
-- ../.lake/packages/CvxLean/CvxLean/Tactic/DCP/AtomLibrary/Fns/Sqrt.lean

end SqrtAtom

namespace TraceAtom

/-! Section 4.5 -/

-- <https://github.com/verified-optimization/CvxLean/blob/main/CvxLean/Tactic/DCP/AtomLibrary/Fns/Trace.lean>
-- ../.lake/packages/CvxLean/CvxLean/Tactic/DCP/AtomLibrary/Fns/Trace.lean

end TraceAtom

namespace Canonization

/-! Section 4.3.2 and 4.5 -/

def p :=
  optimization (x y : ℝ)
    minimize -sqrt (x - y)
    subject to
      c₁ : y = 2 * x - 3
      c₂ : x ^ 2 ≤ 2
      c₃ : 0 ≤ x - y

equivalence eqv/q : p := by
  dcp

#print q
#check eqv

end Canonization

namespace Solving

/-! Section 4.5 -/

open Canonization

solve p

#print p.conicForm -- shows the canonized problem, in conic form
#eval p.status     -- "PRIMAL_AND_DUAL_FEASIBLE"
#eval p.value      -- -2.101003
#eval p.solution   -- (-1.414214, -5.828427)

end Solving

namespace ConnectionToSolver

/-! Section 4.5.1 -/

add_real_to_float : Real.exp := Float.exp

-- We can check as follows.
#real_to_float Real.exp 1

-- CBF file generated:
-- VER
-- 3

-- OBJSENSE
-- MIN

-- VAR
-- 4 1
-- F 4

-- CON
-- 8 4
-- L= 1
-- L+ 1
-- QR 3
-- QR 3

-- OBJACOORD
-- 1
-- 2 -1.000000

-- OBJBCOORD
-- -0.000000

-- ACOORD
-- 8
-- 0 0 2.000000
-- 0 1 -1.000000
-- 1 3 -1.000000
-- 2 0 1.000000
-- 2 1 -1.000000
-- 4 2 1.000000
-- 5 3 1.000000
-- 7 0 1.000000

-- BCOORD
-- 4
-- 0 -3.000000
-- 1 2.000000
-- 3 0.500000
-- 6 0.500000

-- Solution file generated:
-- NAME                :
-- PROBLEM STATUS      : PRIMAL_AND_DUAL_FEASIBLE
-- SOLUTION STATUS     : OPTIMAL
-- OBJECTIVE NAME      : OBJ
-- PRIMAL OBJECTIVE    : -2.10100299e+00
-- DUAL OBJECTIVE      : -2.10100298e+00

-- CONSTRAINTS
-- INDEX      NAME           AT ACTIVITY                 LOWER LIMIT        UPPER LIMIT        DUAL LOWER               DUAL UPPER

-- VARIABLES
-- INDEX      NAME           AT ACTIVITY                 LOWER LIMIT        UPPER LIMIT        DUAL LOWER               DUAL UPPER
-- 0          X1             SB -1.41421354998555e+00    NONE               NONE               0.00000000000000e+00     0.00000000000000e+00
-- 1          X2             SB -5.82842709997110e+00    NONE               NONE               0.00000000000000e+00     0.00000000000000e+00
-- 2          X3             SB 2.10100298624852e+00     NONE               NONE               0.00000000000000e+00     0.00000000000000e+00
-- 3          X4             SB 2.00000000000000e+00     NONE               NONE               0.00000000000000e+00     0.00000000000000e+00

end ConnectionToSolver

end Chapter4

end
