import CvxLean
import CvxLean.Examples.All

noncomputable section

open CvxLean Minimization Real

namespace Chapter6

namespace VehicleSpeedScheduling

/-! 6.2 Vechicle speed scheduling -/

-- <https://github.com/cvxgrp/cvxbook_additional_exercises> (exercise 4.10)

-- Original problem.
#print VehicleSpeedSched.vehSpeedSched

-- Convex problem after the change of variables.
#print VehicleSpeedSched.vehSpeedSchedConvex
#check VehicleSpeedSched.eqv₁

-- Quadratic problem after setting `F(x) := a * x^2 + b * x + c`.
#print VehicleSpeedSched.vehSpeedSchedQuadratic
#check VehicleSpeedSched.eqv₂

#print VehicleSpeedSched.sminₚ
#check VehicleSpeedSched.sminₚ_pos
#check VehicleSpeedSched.aₚdₚ2_nonneg

#eval VehicleSpeedSched.sₚ_opt
-- ![0.955565, 0.955555, 0.955564, 0.955562, 0.955561, 0.955547, 0.912367, 0.960400, 0.912370, 0.912365]

end VehicleSpeedScheduling

namespace FittingSphere

/-! 6.3 Fitting a sphere to data -/

-- <https://github.com/cvxgrp/cvxbook_additional_exercises> (exercise 8.16)

-- Original problem.
#print FittingSphere.fittingSphere

-- Problem after the change of variables.
#print FittingSphere.fittingSphereT
#check FittingSphere.eqv

-- Convex (reduced) problem after removing the constraint.
#print FittingSphere.fittingSphereConvex
#check FittingSphere.red

#eval FittingSphere.cₚ_opt -- ![1.664863, 0.031932]
#eval FittingSphere.rₚ_opt -- 1.159033

end FittingSphere

namespace TrussDesign

/-! 6.4 Truss design -/

-- <https://web.stanford.edu/~boyd/papers/pdf/gp_tutorial.pdf> (6.3)

-- Original problem.
#print TrussDesign.trussDesign

-- Geometric program after the first change of variables.
#print TrussDesign.trussDesignGP
#check TrussDesign.eqv₁

-- Convex problem after the exponential change of variables.
#print TrussDesign.trussDesignConvex
#check TrussDesign.eqv₂

-- DCP problem after `pre_dcp`.
#print TrussDesign.trussDesignDCP
#check TrussDesign.eqv₃

#eval TrussDesign.hₚ_opt -- 1.000000
#eval TrussDesign.wₚ_opt -- 1.000517
#eval TrussDesign.rₚ_opt -- 0.010162
#eval TrussDesign.Rₚ_opt -- 2.121443

end TrussDesign

namespace HypersonicShapeDesign

/-! 6.5 Hypersonic shape design -/

-- <https://www.cvxpy.org/examples/dqcp/hypersonic_shape_design.html>

-- Original problem.
#print HypersonicShapeDesign.hypersonicShapeDesign

-- Convex problem after the change of variables.
#print HypersonicShapeDesign.hypersonicShapeDesignConvex
#check HypersonicShapeDesign.eqv₁

#eval HypersonicShapeDesign.wₚ_opt   -- 0.989524
#eval HypersonicShapeDesign.hₚ_opt   -- 0.144368
#eval HypersonicShapeDesign.ldRatioₚ -- 6.854156

#eval -- false
  let a := HypersonicShapeDesign.aₚ.float;
  let w := HypersonicShapeDesign.wₚ_opt;
  let b := HypersonicShapeDesign.bₚ.float;
  a * (1 / w) - (1 - b) * Float.sqrt (1 - w ^ 2) ≤ 0

-- Further simplified problem.
#print HypersonicShapeDesign.hypersonicShapeDesignSimpler
#check HypersonicShapeDesign.eqv₂

#eval HypersonicShapeDesign.wₚ'_opt   -- 0.989524
#eval HypersonicShapeDesign.hₚ'_opt   -- 0.144371
#eval HypersonicShapeDesign.ldRatioₚ' -- 6.854031

#eval -- true
  let a := HypersonicShapeDesign.aₚ.float;
  let w' := HypersonicShapeDesign.wₚ'_opt;
  let b := HypersonicShapeDesign.bₚ.float;
  a * (1 / w') - (1 - b) * Float.sqrt (1 - w' ^ 2) ≤ 0

end HypersonicShapeDesign

end Chapter6

end
