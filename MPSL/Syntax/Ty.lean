set_option autoImplicit false

namespace MPSL

/-- Types in the embedded assertion language. -/
inductive Ty where
  | loc
  | val
  | iprop
  | empty
  | unit
  | prod (left right : Ty)
  | sum (left right : Ty)
  | arr (domain codomain : Ty)
  deriving DecidableEq, Repr

namespace Ty

def format : Ty -> String
  | .loc => "loc"
  | .val => "val"
  | .iprop => "iProp"
  | .empty => "𝟘"
  | .unit => "𝟙"
  | .prod left right => s!"({left.format} × {right.format})"
  | .sum left right => s!"({left.format} + {right.format})"
  | .arr domain codomain => s!"({domain.format} → {codomain.format})"

end Ty

end MPSL
