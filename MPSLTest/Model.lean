set_option autoImplicit false

namespace MPSL.TestModel

/-- Concrete heap locations used by the test suite. -/
abbrev Location := Nat

/-- Concrete stored values. Locations embed into values through `loc`. -/
inductive Value where
  | loc (location : Location)
  | int (integer : Int)
  | string (string : String)
  deriving DecidableEq, Repr

end MPSL.TestModel
